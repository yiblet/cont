use crate::{InitSans, Sans, step::Step};

/// Run the first continuation to completion, then feed its result to the second.
///
/// The first stage's `Done` value becomes the input to the second stage.
/// Both stages must yield the same type.
pub fn chain<I, O, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Sans<I, O, Done = I>,
    R: Sans<I, O>,
{
    Chain(Some(l), r)
}

pub enum AndThen<S1, S2, F> {
    OnFirst(S1, Option<F>),
    OnSecond(S2),
}

impl<I, O, L, R, F> Sans<I, O> for AndThen<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Done) -> R,
{
    type Done = <R::Next as Sans<I, O>>::Done;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        match self {
            AndThen::OnFirst(l, f) => match l.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(a) => {
                    let r = f.take().expect("AndThen::can only be used once")(a);
                    match r.init() {
                        Step::Yielded((o, next_r)) => {
                            *self = AndThen::OnSecond(next_r);
                            Step::Yielded(o)
                        }
                        Step::Complete(d) => Step::Complete(d),
                    }
                }
            },
            AndThen::OnSecond(r) => r.next(input),
        }
    }
}

/// Chains two stages sequentially.
///
/// Created via `chain()` or `first_chain()`. The first stage is dropped from memory
/// once it completes to free resources.
pub struct Chain<S1, S2>(Option<S1>, S2);

impl<I, O, L, R> Sans<I, O> for Chain<L, R>
where
    L: Sans<I, O, Done = I>,
    R: Sans<I, O>,
{
    type Done = R::Done;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
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
