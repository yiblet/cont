use crate::{InitSans, Sans, Step};

enum PollState<S, O, R> {
    Sans(S),
    SansOutput(O, S),
    Return(R),
    Completed,
}

impl<S, O, R> PollState<S, O, R> {
    fn take_output(&mut self) -> Option<O> {
        match self {
            PollState::SansOutput(_, _) => {
                let s = std::mem::replace(self, PollState::Completed);
                match s {
                    PollState::SansOutput(o, s) => {
                        *self = PollState::Sans(s);
                        Some(o)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn take_return(&mut self) -> Option<R> {
        match self {
            PollState::Return(_) => {
                let r = std::mem::replace(self, PollState::Completed);
                match r {
                    PollState::Return(r) => Some(r),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub struct Pollable<S, O, R> {
    state: PollState<S, O, R>,
}

pub enum Poll<I> {
    Poll,
    Input(I),
}

pub enum PollOutput<I, O> {
    Output(O),
    Complete,
    NeedsInput,
    NeedsPoll(I),
}

#[derive(Debug)]
pub enum PollError {
    AlreadyComplete,
}

impl std::fmt::Display for PollError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PollError::AlreadyComplete => write!(f, "already complete"),
        }
    }
}

impl std::error::Error for PollError {}

/// Create a continuation that polls the wrapped stage for input.
pub fn poll<I, S, O, R>(stage: S) -> Pollable<S, O, R>
where
    S: Sans<I, O>,
{
    Pollable {
        state: PollState::Sans(stage),
    }
}

pub fn init_poll<I, S, O, T>(init: T) -> Pollable<S, O, S::Return>
where
    S: Sans<I, O>,
    T: InitSans<I, O, Next = S>,
{
    match init.init() {
        Step::Yielded((o, s)) => Pollable {
            state: PollState::SansOutput(o, s),
        },
        Step::Complete(r) => Pollable {
            state: PollState::Return(r),
        },
    }
}

impl<I, O, S> Sans<Poll<I>, PollOutput<I, O>> for Pollable<S, O, S::Return>
where
    S: Sans<I, O>,
{
    type Return = Result<S::Return, PollError>;

    fn next(&mut self, input: Poll<I>) -> Step<PollOutput<I, O>, Self::Return> {
        match (&mut self.state, input) {
            (PollState::Sans(_), Poll::Poll) => Step::Yielded(PollOutput::NeedsInput),
            (PollState::Sans(s), Poll::Input(i)) => match s.next(i) {
                Step::Yielded(o) => Step::Yielded(PollOutput::Output(o)),
                Step::Complete(a) => {
                    self.state = PollState::Completed;
                    Step::Complete(Ok(a))
                }
            },
            (PollState::SansOutput(_, _), Poll::Poll) => {
                let o = self.state.take_output().unwrap(); // SAFETY: we know it's in the sans output state
                Step::Yielded(PollOutput::Output(o))
            }
            (PollState::SansOutput(_, _), Poll::Input(i2)) => {
                Step::Yielded(PollOutput::NeedsPoll(i2))
            }
            (PollState::Return(_), Poll::Poll) => {
                let r = self.state.take_return().unwrap(); // SAFETY: we know it's in the return state
                Step::Complete(Ok(r))
            }
            (PollState::Return(_), Poll::Input(i2)) => Step::Yielded(PollOutput::NeedsPoll(i2)),
            (PollState::Completed, _) => Step::Complete(Err(PollError::AlreadyComplete)),
        }
    }
}

// implment InitSans for Pollable
impl<I, O, S> InitSans<Poll<I>, PollOutput<I, O>> for Pollable<S, O, S::Return>
where
    S: Sans<I, O>,
{
    type Next = Self;

    fn init(
        mut self,
    ) -> Step<(PollOutput<I, O>, Self::Next), <Self::Next as Sans<Poll<I>, PollOutput<I, O>>>::Return>
    {
        match self.next(Poll::Poll) {
            Step::Yielded(o) => Step::Yielded((o, self)),
            Step::Complete(r) => Step::Complete(r),
        }
    }
}
