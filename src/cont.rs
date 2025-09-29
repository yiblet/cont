use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::{Arc, Mutex},
};

use either::Either;

/// Core trait for stateful computations that process input and yield intermediate values.
///
/// Each call to `next()` either yields an intermediate result or signals completion.
/// This allows building composable, resumable computations.
///
/// ```rust
/// use cont::*;
///
/// let mut stage = once(|x: i32| x * 2);
/// assert_eq!(stage.next(5).unwrap_left(), 10);
/// assert_eq!(stage.next(3).unwrap_right(), 3); // Done
/// ```
pub trait Cont<A> {
    /// Type of intermediate values yielded during computation
    type Yield;
    /// Type of final result when computation completes
    type Done;

    /// Process input, returning `Left(yield)` to continue or `Right(done)` to complete.
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done>;

    /// Chain with another continuation.
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Cont<A, Done = A>,
        R: Cont<A, Yield = Self::Yield>,
    {
        chain(self, r)
    }

    /// Chain with a function that executes once.
    fn chain_once<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Cont<A, Done = A>,
        F: FnOnce(Self::Done) -> Self::Yield,
    {
        chain(self, Once::new(f))
    }

    /// Chain with a function that repeats indefinitely.
    fn chain_repeat<F>(self, f: F) -> Chain<Self, Repeat<F>>
    where
        Self: Sized + Cont<A, Done = A>,
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

impl<A, C> Cont<A> for Arc<Mutex<C>>
where
    C: Cont<A>,
{
    type Yield = C::Yield;
    type Done = Result<C::Done, PoisonError>;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.lock().map_err(|_| PoisonError) {
            Ok(mut f) => f.next(input).map_right(Ok),
            Err(e) => Either::Right(Err(e)),
        }
    }
}

impl<A, C> Cont<A> for Rc<RefCell<C>>
where
    C: Cont<A>,
{
    type Yield = C::Yield;
    type Done = C::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        let mut v = self.as_ref().borrow_mut();
        v.next(input)
    }
}

pub struct FromFn<F>(F);

impl<A, Y, D, F> Cont<A> for FromFn<F>
where
    F: FnMut(A) -> Either<Y, D>,
{
    type Yield = Y;
    type Done = D;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        (self.0)(input)
    }
}

impl<A, L, R> Cont<A> for Either<L, R>
where
    L: Cont<A>,
    R: Cont<A, Yield = L::Yield, Done = L::Done>,
{
    type Yield = L::Yield;
    type Done = L::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self {
            Either::Left(l) => l.next(input),
            Either::Right(r) => r.next(input),
        }
    }
}

/// Applies a function to each input, yielding results indefinitely.
///
/// Never completes on its own - will continue processing until externally stopped.
pub struct Repeat<F>(F);

impl<A, Y, F> Cont<A> for Repeat<F>
where
    F: FnMut(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        Either::Left(self.0(input))
    }
}

/// Applies a function once, then completes on subsequent calls.
///
/// First call yields the function result, subsequent calls return `Right(input)`.
pub struct Once<F>(Option<F>);

/// Create a continuation that applies a function once.
///
/// ```rust
/// use cont::*;
///
/// let mut stage = once(|x: i32| x + 10);
/// assert_eq!(stage.next(5).unwrap_left(), 15);
/// assert_eq!(stage.next(3).unwrap_right(), 3); // Done
/// ```
pub fn once<F>(f: F) -> Once<F> {
    Once(Some(f))
}

impl<F> Once<F> {
    pub fn new(f: F) -> Once<F> {
        Once(Some(f))
    }
}

impl<A, Y, F> Cont<A> for Once<F>
where
    F: FnOnce(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.0.take() {
            Some(f) => Either::Left(f(input)),
            None => Either::Right(input),
        }
    }
}

/// Run the first continuation to completion, then feed its result to the second.
///
/// The first stage's `Done` value becomes the input to the second stage.
/// Both stages must yield the same type.
pub fn chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Cont<A, Done = A>,
    R: Cont<A, Yield = L::Yield>,
{
    Chain(Some(l), r)
}

/// Chains two stages sequentially.
///
/// Created via `chain()` or `first_chain()`. The first stage is dropped from memory
/// once it completes to free resources.
pub struct Chain<S1, S2>(Option<S1>, S2);

impl<A, L, R> Cont<A> for Chain<L, R>
where
    L: Cont<A, Done = A>,
    R: Cont<A, Yield = L::Yield>,
{
    type Yield = L::Yield;
    type Done = R::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.0 {
            Some(ref mut l) => match l.next(input) {
                Either::Left(y) => Either::Left(y),
                Either::Right(a) => {
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

impl<A1, A2, S, F> Cont<A1> for MapInput<S, F>
where
    S: Cont<A2>,
    F: FnMut(A1) -> A2,
{
    type Yield = S::Yield;
    type Done = S::Done;
    fn next(&mut self, input: A1) -> Either<Self::Yield, Self::Done> {
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

impl<A, Y1, Y2, S, F> Cont<A> for MapYield<S, F>
where
    S: Cont<A, Yield = Y1>,
    F: FnMut(Y1) -> Y2,
{
    type Yield = Y2;
    type Done = S::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Either::Left(y1) => Either::Left((self.f)(y1)),
            Either::Right(a) => Either::Right(a),
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

impl<A, Y, D1, D2, S, F> Cont<A> for MapDone<S, F>
where
    S: Cont<A, Yield = Y, Done = D1>,
    F: FnMut(D1) -> D2,
{
    type Yield = Y;
    type Done = D2;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Either::Left(y) => Either::Left(y),
            Either::Right(r1) => Either::Right((self.f)(r1)),
        }
    }
}

/// Create a continuation that applies a function indefinitely.
///
/// ```rust
/// use cont::*;
///
/// let mut doubler = repeat(|x: i32| x * 2);
/// assert_eq!(doubler.next(5).unwrap_left(), 10);
/// assert_eq!(doubler.next(3).unwrap_left(), 6);
/// // Continues forever...
/// ```
pub fn repeat<A, Y, F: FnMut(A) -> Y>(f: F) -> Repeat<F> {
    Repeat(f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::first::*;

    fn add_three(value: i32) -> i32 {
        value + 3
    }

    #[derive(Clone, Copy, Debug)]
    struct ImmediateFirstDone;

    impl Cont<&'static str> for ImmediateFirstDone {
        type Yield = &'static str;
        type Done = &'static str;

        fn next(&mut self, input: &'static str) -> Either<Self::Yield, Self::Done> {
            Either::Right(input)
        }
    }

    impl First<&'static str> for ImmediateFirstDone {
        type Next = Self;

        fn first(
            self,
        ) -> Either<
            (<Self::Next as Cont<&'static str>>::Yield, Self::Next),
            <Self::Next as Cont<&'static str>>::Done,
        > {
            Either::Right("left-done")
        }
    }

    #[test]
    fn test_simple_addition() {
        let mut prev = 1;
        let fib = first_repeat(1, move |n: u128| {
            let next = prev + n;
            prev = next;
            next
        });

        let (_, mut next) = fib.first().unwrap_left();
        for i in 1..11 {
            let cur = next.next(1).unwrap_left();
            assert_eq!(i + 1, cur);
        }
    }

    #[test]
    fn test_simple_divider() {
        let mut start = 101323012313805546028676730784521326u128;
        let divider = first_repeat(start, |divisor: u128| {
            start /= divisor;
            start
        });

        assert_eq!(size_of_val(&divider), 32);
        let (mut cur, mut next) = divider.first().unwrap_left();
        for i in 2..20 {
            let next_cur = next.next(i).unwrap_left();
            assert_eq!(cur / i, next_cur);
            cur = next_cur;
        }
    }

    #[test]
    fn test_chain_once_into_repeat() {
        let initializer = first_once(10_u32, |input: u32| input + 5);
        let mut multiplier = 2_u32;
        let repeater = repeat(move |input: u32| {
            let output = input * multiplier;
            multiplier += 1;
            output
        });

        let (first_yield, mut stage) = initializer.chain(repeater);
        assert_eq!(10, first_yield);
        assert_eq!(13, stage.next(8).unwrap_left());
        assert_eq!(16, stage.next(8).unwrap_left());
        assert_eq!(24, stage.next(8).unwrap_left());
        assert_eq!(32, stage.next(8).unwrap_left());
    }

    #[test]
    fn test_map_input_and_map_yield_pipeline() {
        let mut total = 0_i64;
        let repeating = first_repeat(0_i64, move |delta: i64| {
            total += delta;
            total
        })
        .map_input(|cmd: &str| -> i64 {
            let mut parts = cmd.split_whitespace();
            let op = parts.next().expect("operation must exist");
            let amount: i64 = parts
                .next()
                .expect("amount must exist")
                .parse()
                .expect("amount must parse");
            match op {
                "add" => amount,
                "sub" => -amount,
                _ => panic!("unsupported op: {op}"),
            }
        })
        .map_yield(|value: i64| format!("total={value}"));

        let (initial_total, mut stage) = repeating;
        assert_eq!("total=0", initial_total);
        assert_eq!("total=5", stage.next("add 5").unwrap_left());
        assert_eq!("total=2", stage.next("sub 3").unwrap_left());
        assert_eq!("total=7", stage.next("add 5").unwrap_left());
    }

    #[test]
    fn test_chain_and_map_done_resume_flow() {
        let initializer = first_once(42_u32, |input: u32| input + 1);
        let finisher = once(|input: u32| input * 3);

        let (first_value, mut stage) = initializer
            .chain(finisher)
            .map_done(|resume: u32| resume + 7);
        assert_eq!(42, first_value);

        assert_eq!(11, stage.next(10).unwrap_left());
        assert_eq!(30, stage.next(10).unwrap_left());
        assert_eq!(17, stage.next(10).unwrap_right());
    }

    #[test]
    fn test_chain_switches_to_second_stage_after_first_done() {
        let mut stage = once(|val: u32| val + 1).chain(repeat(|val: u32| val * 2));

        assert_eq!(stage.next(3).unwrap_left(), 4);
        assert_eq!(stage.next(4).unwrap_left(), 8);
        assert_eq!(stage.next(5).unwrap_left(), 10);
    }

    #[test]
    fn test_chain_propagates_done_from_second_stage() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2));

        assert_eq!(stage.next(2).unwrap_left(), 3);
        assert_eq!(stage.next(3).unwrap_left(), 6);
        assert_eq!(stage.next(4).unwrap_right(), 4);
    }

    #[test]
    fn test_either_first_right_branch_selected() {
        let stage: Either<(i32, Repeat<fn(i32) -> i32>), (i32, Repeat<fn(i32) -> i32>)> =
            Either::Right(first_repeat(2_i32, add_three));

        let (first_value, mut next_stage) = stage.first().unwrap_left();
        assert_eq!(2, first_value);
        assert_eq!(5, next_stage.next(2).unwrap_left());
        assert_eq!(6, next_stage.next(3).unwrap_left());
    }

    #[test]
    fn test_either_first_left_done_returns_resume() {
        let stage: Either<ImmediateFirstDone, ImmediateFirstDone> =
            Either::Left(ImmediateFirstDone);

        let resume = stage.first().unwrap_right();
        assert_eq!("left-done", resume);
    }

    #[test]
    fn test_map_done_applies_after_chain_completion() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2))
            .map_done(|done: u32| format!("resume={done}"));

        assert_eq!(stage.next(5).unwrap_left(), 6);
        assert_eq!(stage.next(6).unwrap_left(), 12);
        assert_eq!(stage.next(7).unwrap_right(), "resume=7".to_string());
    }

    #[test]
    fn test_first_ext_map_input_yield_done() {
        let initializer = first_once(5_u32, |input: u32| input + 2);
        let finisher = once(|value: u32| value * 2);

        let (first_value, mut rest) = initializer
            .chain(finisher)
            .map_input(|text: &str| text.parse::<u32>().expect("number"))
            .map_yield(|value: u32| format!("value={value}"))
            .map_done(|resume: u32| format!("done={resume}"));
        assert_eq!("value=5", first_value);
        assert_eq!("value=9", rest.next("7").unwrap_left());
        assert_eq!("value=16", rest.next("8").unwrap_left());
        assert_eq!("done=9", rest.next("9").unwrap_right());
    }
}
