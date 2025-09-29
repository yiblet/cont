use either::Either;
use crate::{Cont, Chain, MapInput, MapYield, MapDone, once, repeat, chain, Once, Repeat};

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

/// Extension methods for chaining and transforming first stages.
///
/// Implemented for tuples (Y, S) where S is a continuation.
pub trait FirstExt<A, Y, S: Cont<A>> {
    /// Chain with a continuation.
    fn chain<R>(self, r: R) -> (Y, Chain<S, R>)
    where
        S: Cont<A, Done = A>,
        R: Cont<A, Yield = Y>;

    /// Chain with a function that executes once.
    fn chain_once<F>(self, f: F) -> (Y, Chain<S, Once<F>>)
    where
        S: Cont<A, Done = A>,
        F: FnOnce(S::Done) -> Y;

    /// Chain with a function that repeats indefinitely.
    fn chain_repeat<F>(self, f: F) -> (Y, Chain<S, Repeat<F>>)
    where
        S: Cont<A, Done = A>,
        F: FnMut(S::Done) -> Y;

    /// Transform inputs before they reach the underlying continuation.
    fn map_input<A2, F>(self, f: F) -> (Y, MapInput<S, F>)
    where
        F: FnMut(A2) -> A;

    /// Transform yielded values before returning them.
    fn map_yield<Y2, F>(self, f: F) -> (Y2, MapYield<S, F>)
    where
        F: FnMut(Y) -> Y2;

    /// Transform the final result when completing.
    fn map_done<D2, F>(self, f: F) -> (Y, MapDone<S, F>)
    where
        F: FnMut(S::Done) -> D2;
}

impl<A, Y, S: Cont<A, Yield = Y>> FirstExt<A, Y, S> for (Y, S) {
    fn chain<R>(self, r: R) -> (Y, Chain<S, R>)
    where
        S: Cont<A, Done = A>,
        R: Cont<A, Yield = Y>,
    {
        first_chain(self, r)
    }

    fn chain_once<F>(self, f: F) -> (Y, Chain<S, Once<F>>)
    where
        S: Cont<A, Done = A>,
        F: FnOnce(S::Done) -> Y,
    {
        first_chain(self, once(f))
    }

    fn chain_repeat<F>(self, f: F) -> (Y, Chain<S, Repeat<F>>)
    where
        S: Cont<A, Done = A>,
        F: FnMut(S::Done) -> Y,
    {
        first_chain(self, repeat(f))
    }

    fn map_input<A2, F>(self, f: F) -> (Y, MapInput<S, F>)
    where
        F: FnMut(A2) -> A,
    {
        (self.0, MapInput { f, stage: self.1 })
    }

    fn map_yield<Y2, F>(self, mut f: F) -> (Y2, MapYield<S, F>)
    where
        F: FnMut(Y) -> Y2,
    {
        let mapped_y = f(self.0);
        (mapped_y, MapYield { f, stage: self.1 })
    }

    fn map_done<D2, F>(self, f: F) -> (Y, MapDone<S, F>)
    where
        F: FnMut(S::Done) -> D2,
    {
        (self.0, MapDone { f, stage: self.1 })
    }
}
