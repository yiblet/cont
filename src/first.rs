use crate::{Chain, Cont, MapDone, MapInput, MapYield, Once, Repeat, chain, once, repeat};
use either::Either;

/// Computations that yield an initial value before processing input.
///
/// Unlike `Cont`, `First` stages can produce output immediately, making them ideal
/// for pipeline initialization or generators with seed values.
///
/// ```rust
/// use cont::*;
///
/// let stage = first_once(42, |x: i32| x + 1);
/// let (initial, mut cont) = stage.first().unwrap_left();
/// assert_eq!(initial, 42);
/// ```
pub trait First<A> {
    type Next: Cont<A>;

    /// Execute the first stage.
    ///
    /// Returns `Left((yield_value, continuation))` for normal execution,
    /// or `Right(done_value)` if the computation completes immediately.
    #[allow(clippy::type_complexity)]
    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done>;

    /// Chain with a continuation.
    fn chain<R>(self, r: R) -> (<Self::Next as Cont<A>>::Yield, Chain<Self::Next, R>)
    where
        Self: Sized,
        Self::Next: Cont<A, Done = A>,
        R: Cont<A, Yield = <Self::Next as Cont<A>>::Yield>,
    {
        match self.first() {
            Either::Left((y, next)) => (y, chain(next, r)),
            Either::Right(_) => panic!("First stage completed immediately, cannot chain"),
        }
    }

    /// Chain with a function that executes once.
    fn chain_once<F>(self, f: F) -> (<Self::Next as Cont<A>>::Yield, Chain<Self::Next, Once<F>>)
    where
        Self: Sized,
        Self::Next: Cont<A, Done = A>,
        F: FnOnce(<Self::Next as Cont<A>>::Done) -> <Self::Next as Cont<A>>::Yield,
    {
        self.chain(once(f))
    }

    /// Chain with a function that repeats indefinitely.
    fn chain_repeat<F>(self, f: F) -> (<Self::Next as Cont<A>>::Yield, Chain<Self::Next, Repeat<F>>)
    where
        Self: Sized,
        Self::Next: Cont<A, Done = A>,
        F: FnMut(<Self::Next as Cont<A>>::Done) -> <Self::Next as Cont<A>>::Yield,
    {
        self.chain(repeat(f))
    }

    /// Transform inputs before they reach the underlying continuation.
    fn map_input<A2, F>(self, f: F) -> (<Self::Next as Cont<A>>::Yield, MapInput<Self::Next, F>)
    where
        Self: Sized,
        F: FnMut(A2) -> A,
    {
        match self.first() {
            Either::Left((y, next)) => (y, MapInput { f, stage: next }),
            Either::Right(_) => panic!("First stage completed immediately, cannot map input"),
        }
    }

    /// Transform yielded values before returning them.
    fn map_yield<Y2, F>(self, mut f: F) -> (Y2, MapYield<Self::Next, F>)
    where
        Self: Sized,
        F: FnMut(<Self::Next as Cont<A>>::Yield) -> Y2,
    {
        match self.first() {
            Either::Left((y, next)) => {
                let mapped_y = f(y);
                (mapped_y, MapYield { f, stage: next })
            }
            Either::Right(_) => panic!("First stage completed immediately, cannot map yield"),
        }
    }

    /// Transform the final result when completing.
    fn map_done<D2, F>(self, f: F) -> (<Self::Next as Cont<A>>::Yield, MapDone<Self::Next, F>)
    where
        Self: Sized,
        F: FnMut(<Self::Next as Cont<A>>::Done) -> D2,
    {
        match self.first() {
            Either::Left((y, next)) => (y, MapDone { f, stage: next }),
            Either::Right(_) => panic!("First stage completed immediately, cannot map done"),
        }
    }
}

impl<A, Y, F> First<A> for (Y, F)
where
    F: Cont<A, Yield = Y>,
{
    type Next = F;
    fn first(self) -> Either<(Y, F), F::Done> {
        Either::Left(self)
    }
}

impl<A, L, R> First<A> for Either<L, R>
where
    L: First<A>,
    R: First<A>,
    R::Next: Cont<A, Done = <L::Next as Cont<A>>::Done, Yield = <L::Next as Cont<A>>::Yield>,
{
    type Next = Either<L::Next, R::Next>;
    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        match self {
            Either::Left(l) => match l.first() {
                Either::Left((y, next_l)) => Either::Left((y, Either::Left(next_l))),
                Either::Right(resume) => Either::Right(resume),
            },
            Either::Right(r) => match r.first() {
                Either::Left((y, next_r)) => Either::Left((y, Either::Right(next_r))),
                Either::Right(resume) => Either::Right(resume),
            },
        }
    }
}

/// Chain a `First` stage with a continuation.
///
/// Allows connecting stages that have initial yields with regular continuations.
pub fn first_chain<A, Y, L, R>(first: (Y, L), r: R) -> (Y, Chain<L, R>)
where
    L: Cont<A, Done = A, Yield = Y>,
    R: Cont<A, Yield = Y>,
{
    (first.0, chain(first.1, r))
}

/// Yield an initial value, then apply a function once.
///
/// Combines immediate output with single function application.
pub fn first_once<A, Y, F: FnOnce(A) -> Y>(y: Y, f: F) -> (Y, Once<F>) {
    (y, once(f))
}

/// Yield an initial value, then apply a function indefinitely.
///
/// Useful for generators that need to emit a seed value before starting their loop.
pub fn first_repeat<A, Y, F: FnMut(A) -> Y>(y: Y, f: F) -> (Y, Repeat<F>) {
    (y, repeat(f))
}
