use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::{Arc, Mutex},
};

use crate::step::Step;

/// Core trait for stateful computations that process input and yield intermediate values.
///
/// Each call to `next()` either yields an intermediate result or signals completion.
/// This allows building composable, resumable computations.
///
/// ```rust
/// use cont::*;
///
/// let mut stage = once(|x: i32| x * 2);
/// assert_eq!(stage.next(5).unwrap_yielded(), 10);
/// assert_eq!(stage.next(3).unwrap_complete(), 3); // Done
/// ```
pub trait Sans<A> {
    /// Type of intermediate values yielded during computation
    type Yield;
    /// Type of final result when computation completes
    type Done;

    /// Process input, returning `Yield` to continue or `Done` to complete.
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done>;

    /// Chain with another continuation.
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Sans<A, Done = A>,
        R: Sans<A, Yield = Self::Yield>,
    {
        chain(self, r)
    }

    /// Chain with a function that executes once.
    fn chain_once<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Sans<A, Done = A>,
        F: FnOnce(Self::Done) -> Self::Yield,
    {
        chain(self, Once::new(f))
    }

    /// Chain with a function that repeats indefinitely.
    fn chain_repeat<F>(self, f: F) -> Chain<Self, Repeat<F>>
    where
        Self: Sized + Sans<A, Done = A>,
        F: FnMut(Self::Done) -> Self::Yield,
    {
        chain(self, repeat(f))
    }

    /// Transform inputs before they reach this continuation.
    fn map_input<A2, F>(self, f: F) -> MapInput<Self, F>
    where
        Self: Sized,
        F: FnMut(A2) -> A,
    {
        MapInput { f, stage: self }
    }

    /// Transform yielded values before returning them.
    fn map_yield<Y2, F>(self, f: F) -> MapYield<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Yield) -> Y2,
    {
        MapYield { f, stage: self }
    }

    /// Transform the final result when completing.
    fn map_done<D2, F>(self, f: F) -> MapDone<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Done) -> D2,
    {
        MapDone { f, stage: self }
    }
}

#[derive(Debug)]
pub struct PoisonError;

impl fmt::Display for PoisonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "lock was poisoned")
    }
}

impl std::error::Error for PoisonError {}

impl<A, C> Sans<A> for Arc<Mutex<C>>
where
    C: Sans<A>,
{
    type Yield = C::Yield;
    type Done = Result<C::Done, PoisonError>;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self.lock().map_err(|_| PoisonError) {
            Ok(mut f) => f.next(input).map_complete(Ok),
            Err(e) => Step::Complete(Err(e)),
        }
    }
}

impl<A, C> Sans<A> for Rc<RefCell<C>>
where
    C: Sans<A>,
{
    type Yield = C::Yield;
    type Done = C::Done;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        let mut v = self.as_ref().borrow_mut();
        v.next(input)
    }
}

pub struct FromFn<F>(pub F);

impl<A, Y, D, F> Sans<A> for FromFn<F>
where
    F: FnMut(A) -> Step<Y, D>,
{
    type Yield = Y;
    type Done = D;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        (self.0)(input)
    }
}

impl<A, L, R> Sans<A> for either::Either<L, R>
where
    L: Sans<A>,
    R: Sans<A, Yield = L::Yield, Done = L::Done>,
{
    type Yield = L::Yield;
    type Done = L::Done;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self {
            either::Either::Left(l) => l.next(input),
            either::Either::Right(r) => r.next(input),
        }
    }
}

/// Applies a function to each input, yielding results indefinitely.
///
/// Never completes on its own - will continue processing until externally stopped.
pub struct Repeat<F>(F);

impl<A, Y, F> Sans<A> for Repeat<F>
where
    F: FnMut(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        Step::Yielded(self.0(input))
    }
}

/// Applies a function once, then completes on subsequent calls.
///
/// First call yields the function result, subsequent calls return `Done(input)`.
pub struct Once<F>(Option<F>);

/// Create a continuation that applies a function once.
///
/// ```rust
/// use cont::*;
///
/// let mut stage = once(|x: i32| x + 10);
/// assert_eq!(stage.next(5).unwrap_yielded(), 15);
/// assert_eq!(stage.next(3).unwrap_complete(), 3); // Done
/// ```
pub fn once<F>(f: F) -> Once<F> {
    Once(Some(f))
}

impl<F> Once<F> {
    pub fn new(f: F) -> Once<F> {
        Once(Some(f))
    }
}

impl<A, Y, F> Sans<A> for Once<F>
where
    F: FnOnce(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self.0.take() {
            Some(f) => Step::Yielded(f(input)),
            None => Step::Complete(input),
        }
    }
}

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

/// Transforms input before passing it to the wrapped stage.
///
/// Useful for adapting between different input types or preprocessing data.
pub struct MapInput<S, F> {
    pub f: F,
    pub stage: S,
}

impl<A1, A2, S, F> Sans<A1> for MapInput<S, F>
where
    S: Sans<A2>,
    F: FnMut(A1) -> A2,
{
    type Yield = S::Yield;
    type Done = S::Done;
    fn next(&mut self, input: A1) -> Step<Self::Yield, Self::Done> {
        let a2 = (self.f)(input);
        self.stage.next(a2)
    }
}

/// Transforms yielded values from the wrapped stage.
///
/// Allows converting or formatting output without changing the underlying computation.
pub struct MapYield<S, F> {
    pub f: F,
    pub stage: S,
}

impl<A, Y1, Y2, S, F> Sans<A> for MapYield<S, F>
where
    S: Sans<A, Yield = Y1>,
    F: FnMut(Y1) -> Y2,
{
    type Yield = Y2;
    type Done = S::Done;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Step::Yielded(y1) => Step::Yielded((self.f)(y1)),
            Step::Complete(a) => Step::Complete(a),
        }
    }
}

/// Transforms the final result from the wrapped stage.
///
/// Applied only when the computation completes, not to intermediate yields.
pub struct MapDone<S, F> {
    pub f: F,
    pub stage: S,
}

impl<A, Y, D1, D2, S, F> Sans<A> for MapDone<S, F>
where
    S: Sans<A, Yield = Y, Done = D1>,
    F: FnMut(D1) -> D2,
{
    type Yield = Y;
    type Done = D2;
    fn next(&mut self, input: A) -> Step<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Step::Yielded(y) => Step::Yielded(y),
            Step::Complete(r1) => Step::Complete((self.f)(r1)),
        }
    }
}

/// Create a continuation that applies a function indefinitely.
///
/// ```rust
/// use cont::*;
///
/// let mut doubler = repeat(|x: i32| x * 2);
/// assert_eq!(doubler.next(5).unwrap_yielded(), 10);
/// assert_eq!(doubler.next(3).unwrap_yielded(), 6);
/// // Continues forever...
/// ```
pub fn repeat<A, Y, F: FnMut(A) -> Y>(f: F) -> Repeat<F> {
    Repeat(f)
}

/// Create a continuation from a closure.
///
/// ```rust
/// use cont::*;
///
/// let mut toggle = from_fn(|x: bool| {
///     if x { Step::Yielded(!x) } else { Step::Complete(x) }
/// });
/// assert_eq!(toggle.next(true).unwrap_yielded(), false);
/// assert_eq!(toggle.next(false).unwrap_complete(), false);
/// ```
pub fn from_fn<F>(f: F) -> FromFn<F> {
    FromFn(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chain_switches_to_second_stage_after_first_done() {
        let mut stage = once(|val: u32| val + 1).chain(repeat(|val: u32| val * 2));

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

    #[test]
    fn test_map_done_applies_after_chain_completion() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2))
            .map_done(|done: u32| format!("resume={done}"));

        assert_eq!(stage.next(5).unwrap_yielded(), 6);
        assert_eq!(stage.next(6).unwrap_yielded(), 12);
        assert_eq!(stage.next(7).unwrap_complete(), "resume=7".to_string());
    }
}
