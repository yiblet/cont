#![allow(dead_code)] // new join implementation is not yet stable
use crate::{InitSans, Sans, Step};

pub fn many<const N: usize, I, O, S>(rest: [S; N]) -> Many<N, S>
where
    S: Sans<I, O, Return = I>,
{
    Many {
        states: rest.map(|r| Some(r)),
        index: 0,
    }
}

pub struct Many<const N: usize, S> {
    states: [Option<S>; N],
    index: usize,
}

impl<const N: usize, I, O, S> Sans<I, O> for Many<N, S>
where
    S: Sans<I, O, Return = I>,
{
    type Return = S::Return;
    fn next(&mut self, mut input: I) -> Step<O, Self::Return> {
        loop {
            match self.states.get_mut(self.index) {
                Some(Some(s)) => match s.next(input) {
                    Step::Yielded(o) => return Step::Yielded(o),
                    Step::Complete(a) => {
                        self.index += 1;
                        input = a;
                    }
                },
                Some(None) => {
                    self.index += 1;
                }
                None => return Step::Complete(input),
            }
        }
    }
}

fn init_join<const N: usize, I, O, S, T>(rest: [T; N]) -> Join<N, S, O, S::Return>
where
    T: InitSans<I, O, Next = S>,
    S: Sans<I, O>,
{
    let mut complete = 0;
    let rest = rest.map(|s| match s.init() {
        Step::Yielded((o, s)) => JoinState::SansYield(o, s),
        Step::Complete(d) => {
            complete += 1;
            JoinState::Return(d)
        }
    });

    Join {
        state: rest,
        last_index: 0,
        complete,
        completed: false,
    }
}

fn join<const N: usize, I, O, S>(rest: [S; N]) -> Join<N, S, O, S::Return>
where
    S: Sans<I, O>,
{
    Join {
        state: rest.map(|r| JoinState::Sans(r)),
        last_index: 0,
        complete: 0,
        completed: false,
    }
}

enum JoinState<S, Y, R> {
    Sans(S),
    SansYield(Y, S),
    Return(R),
    Returned,
}

impl<S, Y, R> JoinState<S, Y, R> {
    fn take_return(&mut self) -> Option<R> {
        match self {
            JoinState::Return(_) => {
                let r = std::mem::replace(self, JoinState::Returned);
                match r {
                    JoinState::Return(r) => Some(r),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn take_yield(&mut self) -> Option<Y> {
        match self {
            JoinState::SansYield(_, _) => {
                let state = std::mem::replace(self, JoinState::Returned);
                match state {
                    JoinState::SansYield(y, s) => {
                        *self = JoinState::Sans(s);
                        Some(y)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

struct Join<const N: usize, S, Y, R> {
    state: [JoinState<S, Y, R>; N],
    last_index: usize,
    complete: usize,
    completed: bool,
}

#[derive(Debug)]
enum JoinError {
    InvalidState(usize),
    InputEmpty(usize),
    AlreadyReturned(usize),
    AlreadyComplete,
}

impl std::fmt::Display for JoinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JoinError::InvalidState(i) => write!(f, "invalid state for sans at index {}", i),
            JoinError::InputEmpty(i) => write!(f, "input empty at index {}", i),
            JoinError::AlreadyReturned(i) => write!(f, "already returned at index {}", i),
            JoinError::AlreadyComplete => write!(f, "already complete"),
        }
    }
}

impl std::error::Error for JoinError {}

struct JoinEnvelope<T>(usize, T);

impl<T> JoinEnvelope<T> {
    pub fn map<U, F>(self, f: F) -> JoinEnvelope<U>
    where
        F: FnOnce(T) -> U,
    {
        JoinEnvelope(self.0, f(self.1))
    }
}

impl<T> std::ops::Deref for JoinEnvelope<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

enum JoinPoll<T> {
    Poll,
    Complete,
    Input(JoinEnvelope<T>),
}

enum JoinPollOutput<T> {
    AllWaiting,
    AllComplete,
    SomeIncomplete,
    Complete(usize),
    Output(JoinEnvelope<T>),
}

impl<const N: usize, I, O, S> Sans<JoinPoll<I>, JoinPollOutput<O>> for Join<N, S, O, S::Return>
where
    S: Sans<I, O>,
{
    type Return = Result<[S::Return; N], JoinError>;

    fn next(&mut self, input: JoinPoll<I>) -> Step<JoinPollOutput<O>, Self::Return> {
        match input {
            JoinPoll::Poll => {
                for i in 0..N {
                    let idx = (self.last_index + 1 + i) % N;
                    if let Some(y) = self.state.get_mut(idx).and_then(|s| s.take_yield()) {
                        self.last_index = idx;
                        return Step::Yielded(JoinPollOutput::Output(JoinEnvelope(idx, y)));
                    }
                }
                Step::Yielded(JoinPollOutput::AllWaiting)
            }

            JoinPoll::Input(JoinEnvelope(idx, input)) => {
                let state = self.state.get_mut(idx);
                match state {
                    Some(JoinState::Sans(s)) => match s.next(input) {
                        Step::Yielded(o) => {
                            Step::Yielded(JoinPollOutput::Output(JoinEnvelope(idx, o)))
                        }
                        Step::Complete(a) => {
                            if let Some(js) = state {
                                *js = JoinState::Return(a);
                            }
                            self.complete += 1;
                            Step::Yielded(JoinPollOutput::Complete(idx))
                        }
                    },
                    _ => Step::Complete(Err(JoinError::InvalidState(idx))),
                }
            }
            JoinPoll::Complete => {
                if self.complete == N {
                    if self.completed {
                        return Step::Complete(Err(JoinError::AlreadyComplete));
                    }

                    let res: [S::Return; N] = std::array::from_fn(|i| {
                        // SAFETY: self.complete == N so we know all states should be completed
                        self.state.get_mut(i).and_then(|s| s.take_return()).unwrap()
                    });
                    self.completed = true;
                    Step::Complete(Ok(res))
                } else {
                    Step::Yielded(JoinPollOutput::SomeIncomplete)
                }
            }
        }
    }
}

// also implement InitSans for Join
impl<const N: usize, I, O, S> InitSans<JoinPoll<I>, JoinPollOutput<O>> for Join<N, S, O, S::Return>
where
    S: Sans<I, O>,
{
    type Next = Self;

    fn init(
        mut self,
    ) -> Step<
        (JoinPollOutput<O>, Self::Next),
        <Self::Next as Sans<JoinPoll<I>, JoinPollOutput<O>>>::Return,
    > {
        match self.next(JoinPoll::Poll) {
            Step::Yielded(o) => Step::Yielded((o, self)),
            Step::Complete(r) => Step::Complete(r),
        }
    }
}
