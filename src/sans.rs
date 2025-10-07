use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::{Arc, Mutex},
};

use crate::{
    InitSans,
    combinators::{AndThen, Chain, MapDone, MapInput, MapYield, Once, Repeat, chain, once, repeat},
    step::Step,
};

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
pub trait Sans<I, O> {
    /// Type of final result when computation completes
    type Done;

    /// Process input, returning `Yield` to continue or `Done` to complete.
    fn next(&mut self, input: I) -> Step<O, Self::Done>;

    fn and_then<R, F>(self, f: F) -> AndThen<Self, R::Next, F>
    where
        Self: Sized + Sans<I, O, Done = I>,
        R: InitSans<I, O>,
        R::Next: Sans<I, O>,
        F: FnOnce(Self::Done) -> R,
    {
        AndThen::OnFirst(self, Some(f))
    }

    fn boxed(self) -> Box<dyn Sans<I, O, Done = Self::Done>>
    where
        Self: Sized + 'static,
    {
        Box::new(self)
    }

    /// Chain with another continuation.
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Sans<I, O, Done = I>,
        R: Sans<I, O>,
    {
        chain(self, r)
    }

    /// Chain with a function that executes once.
    fn chain_once<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Sans<I, O, Done = I>,
        F: FnOnce(Self::Done) -> O,
    {
        chain(self, once(f))
    }

    /// Chain with a function that repeats indefinitely.
    fn chain_repeat<F>(self, f: F) -> Chain<Self, Repeat<F>>
    where
        Self: Sized + Sans<I, O, Done = I>,
        F: FnMut(Self::Done) -> O,
    {
        chain(self, repeat(f))
    }

    /// Transform inputs before they reach this continuation.
    fn map_input<I2, F>(self, f: F) -> MapInput<Self, F>
    where
        Self: Sized,
        F: FnMut(I2) -> I,
    {
        crate::combinators::map::map_input(f, self)
    }

    /// Transform yielded values before returning them.
    fn map_yield<O2, F>(self, f: F) -> MapYield<Self, F, I, O>
    where
        Self: Sized,
        F: FnMut(O) -> O2,
    {
        crate::combinators::map::map_yield(f, self)
    }

    /// Transform the final result when completing.
    fn map_done<D2, F>(self, f: F) -> MapDone<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Done) -> D2,
    {
        crate::combinators::map::map_done(f, self)
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

impl<I, O, C> Sans<I, O> for Arc<Mutex<C>>
where
    C: Sans<I, O>,
{
    type Done = Result<C::Done, PoisonError>;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        match self.lock().map_err(|_| PoisonError) {
            Ok(mut f) => f.next(input).map_complete(Ok),
            Err(e) => Step::Complete(Err(e)),
        }
    }
}

impl<I, O, C> Sans<I, O> for Rc<RefCell<C>>
where
    C: Sans<I, O>,
{
    type Done = C::Done;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        let mut v = self.as_ref().borrow_mut();
        v.next(input)
    }
}

impl<I, O, L, R> Sans<I, O> for either::Either<L, R>
where
    L: Sans<I, O>,
    R: Sans<I, O, Done = L::Done>,
{
    type Done = L::Done;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        match self {
            either::Either::Left(l) => l.next(input),
            either::Either::Right(r) => r.next(input),
        }
    }
}

impl<I, O, D> Sans<I, O> for Box<dyn Sans<I, O, Done = D>> {
    type Done = D;

    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        (**self).next(input)
    }
}

impl<I, O, D> Sans<I, O> for &'_ mut dyn Sans<I, O, Done = D> {
    type Done = D;

    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        (*self).next(input)
    }
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
