use crate::{Chain, Cont, FromFn, MapDone, MapInput, MapYield, Once, Repeat, chain, once, repeat};
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

/// Yield an initial value, then create a continuation from a closure.
///
/// ```rust
/// use cont::*;
/// use either::Either;
///
/// let mut counter = 0;
/// let (initial, mut stage) = first_from_fn(42, move |x: i32| {
///     counter += 1;
///     if counter < 3 { Either::Left(x * counter) } else { Either::Right(x + counter) }
/// });
/// assert_eq!(initial, 42);
/// assert_eq!(stage.next(10).unwrap_left(), 10);
/// assert_eq!(stage.next(10).unwrap_left(), 20);
/// assert_eq!(stage.next(10).unwrap_right(), 13);
/// ```
pub fn first_from_fn<A, Y, D, F>(initial: Y, f: F) -> (Y, FromFn<F>)
where
    F: FnMut(A) -> Either<Y, D>
{
    (initial, FromFn(f))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of_val;

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
