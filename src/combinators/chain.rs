use crate::{InitSans, Sans, step::Step};

/// Run the first continuation to completion, then feed its result to the second.
///
/// The first stage's `Done` value becomes the input to the second stage.
/// Both stages must yield the same type.
pub fn chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Sans<A, Done = A>,
    R: Sans<A, Yield = L::Yield>,
{
    Chain(Some(l), r)
}

pub enum AndThen<S1, S2, F> {
    OnFirst(S1, Option<F>),
    OnSecond(S2),
}

impl<A, L, R, F> Sans<A> for AndThen<L, R::Next, F>
where
    L: Sans<A>,
    R: InitSans<A>,
    R::Next: Sans<A, Yield = L::Yield>,
    F: FnOnce(L::Done) -> R,
{
    type Yield = L::Yield;
    type Done = <R::Next as Sans<A>>::Done;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self {
            AndThen::OnFirst(l, f) => match l.next(input) {
                Step::Yielded(y) => Step::Yielded(y),
                Step::Complete(a) => {
                    let r = f.take().expect("AndThen::can only be used once")(a);
                    match r.first() {
                        Step::Yielded((y, next_r)) => {
                            *self = AndThen::OnSecond(next_r);
                            Step::Yielded(y)
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

impl<A, L, R> Sans<A> for Chain<L, R>
where
    L: Sans<A, Done = A>,
    R: Sans<A, Yield = L::Yield>,
{
    type Yield = L::Yield;
    type Done = R::Done;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self.0 {
            Some(ref mut l) => match l.next(input) {
                Step::Yielded(y) => Step::Yielded(y),
                Step::Complete(a) => {
                    self.0 = None; // we drop the old stage when it's done
                    self.1.next(a)
                }
            },
            None => self.1.next(input),
        }
    }
}
