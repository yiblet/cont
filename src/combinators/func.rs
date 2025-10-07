use crate::{Sans, step::Step};

pub struct FromFn<F>(F);

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
