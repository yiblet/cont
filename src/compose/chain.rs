use crate::{InitSans, Sans, step::Step};

pub struct AndThen<S1, S2, F> {
    state: AndThenState<S1, S2, F>,
}

impl<I, O, L, R, F> Sans<I, O> for AndThen<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    type Return = <R::Next as Sans<I, O>>::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        self.state.next(input)
    }
}

enum AndThenState<S1, S2, F> {
    OnFirst(S1, Option<F>),
    OnSecond(S2),
}

impl<I, O, L, R, F> Sans<I, O> for AndThenState<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    type Return = <R::Next as Sans<I, O>>::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self {
            AndThenState::OnFirst(l, f) => match l.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(a) => {
                    let r = f.take().expect("AndThen::can only be used once")(a);
                    match r.init() {
                        Step::Yielded((o, next_r)) => {
                            *self = AndThenState::OnSecond(next_r);
                            Step::Yielded(o)
                        }
                        Step::Complete(d) => Step::Complete(d),
                    }
                }
            },
            AndThenState::OnSecond(r) => r.next(input),
        }
    }
}

pub fn and_then<I, O, L, R, F>(l: L, f: F) -> AndThen<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    AndThen {
        state: AndThenState::OnFirst(l, Some(f)),
    }
}

/// Run the first continuation to completion, then feed its result to the second.
///
/// The first stage's `Done` value becomes the input to the second stage.
/// Both stages must yield the same type.
pub fn chain<I, O, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Sans<I, O, Return = I>,
    R: Sans<I, O>,
{
    Chain(Some(l), r)
}

/// Chains two stages sequentially.
///
/// Created via `chain()` or `first_chain()`. The first stage is dropped from memory
/// once it completes to free resources.
pub struct Chain<S1, S2>(Option<S1>, S2);

impl<I, O, L, R> Sans<I, O> for Chain<L, R>
where
    L: Sans<I, O, Return = I>,
    R: Sans<I, O>,
{
    type Return = R::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self.0 {
            Some(ref mut l) => match l.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(a) => {
                    self.0 = None; // we drop the old stage when it's done
                    self.1.next(a)
                }
            },
            None => self.1.next(input),
        }
    }
}

/// Chain an `InitSans` stage with a continuation.
///
/// Allows connecting stages that have initial yields with regular continuations.
pub fn init_chain<I, O, L, R>(first: (O, L), r: R) -> (O, Chain<L, R>)
where
    L: Sans<I, O, Return = I>,
    R: Sans<I, O>,
{
    (first.0, chain(first.1, r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::{once, repeat};

    #[test]
    fn test_chain_switches_to_second_stage_after_first_done() {
        let mut stage = chain(once(|val: u32| val + 1), repeat(|val: u32| val * 2));

        assert_eq!(stage.next(3).unwrap_yielded(), 4);
        assert_eq!(stage.next(4).unwrap_yielded(), 8);
        assert_eq!(stage.next(5).unwrap_yielded(), 10);
    }

    #[test]
    fn test_chain_propagates_done_from_second_stage() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2));

        assert_eq!(stage.next(2).unwrap_yielded(), 3);
        assert_eq!(stage.next(3).unwrap_yielded(), 6);
        assert_eq!(stage.next(4).unwrap_complete(), 4);
    }
}
