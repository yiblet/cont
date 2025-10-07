use crate::{
    Chain, FromFn, MapDone, MapInput, MapYield, Once, Repeat, Sans, Step, chain, from_fn, map_done,
    map_input, map_yield, once, repeat,
};

/// Computations that yield an initial value before processing input.
///
/// Unlike `Sans`, `InitSans` stages can produce output immediately, making them ideal
/// for pipeline initialization or generators with seed values.
///
/// ```rust
/// use cont::*;
///
/// let stage = init_once(42, |x: i32| x + 1);
/// let (initial, mut cont) = stage.init().unwrap_yielded();
/// assert_eq!(initial, 42);
/// ```
pub trait InitSans<I, O> {
    type Next: Sans<I, O>;

    /// Execute the first stage.
    ///
    /// Returns `Yield((yield_value, continuation))` for normal execution,
    /// or `Done(done_value)` if the computation completes immediately.
    #[allow(clippy::type_complexity)]
    fn init(self) -> Step<(O, Self::Next), <Self::Next as Sans<I, O>>::Done>;

    /// Chain with a continuation.
    #[allow(clippy::type_complexity)]
    fn chain<R>(self, r: R) -> Step<(O, Chain<Self::Next, R>), <Self::Next as Sans<I, O>>::Done>
    where
        Self: Sized,
        Self::Next: Sans<I, O, Done = I>,
        R: Sans<I, O>,
    {
        match self.init() {
            Step::Yielded((o, next)) => Step::Yielded((o, chain(next, r))),
            Step::Complete(d) => Step::Complete(d),
        }
    }

    /// Chain with a function that executes once.
    #[allow(clippy::type_complexity)]
    fn chain_once<F>(
        self,
        f: F,
    ) -> Step<(O, Chain<Self::Next, Once<F>>), <Self::Next as Sans<I, O>>::Done>
    where
        Self: Sized,
        Self::Next: Sans<I, O, Done = I>,
        F: FnOnce(<Self::Next as Sans<I, O>>::Done) -> O,
    {
        self.chain(once(f))
    }

    /// Chain with a function that repeats indefinitely.
    #[allow(clippy::type_complexity)]
    fn chain_repeat<F>(
        self,
        f: F,
    ) -> Step<(O, Chain<Self::Next, Repeat<F>>), <Self::Next as Sans<I, O>>::Done>
    where
        Self: Sized,
        Self::Next: Sans<I, O, Done = I>,
        F: FnMut(<Self::Next as Sans<I, O>>::Done) -> O,
    {
        self.chain(repeat(f))
    }

    /// Transform inputs before they reach the underlying continuation.
    #[allow(clippy::type_complexity)]
    fn map_input<I2, F>(
        self,
        f: F,
    ) -> Step<(O, MapInput<Self::Next, F>), <Self::Next as Sans<I, O>>::Done>
    where
        Self: Sized,
        F: FnMut(I2) -> I,
    {
        match self.init() {
            Step::Yielded((o, next)) => Step::Yielded((o, map_input(f, next))),
            Step::Complete(d) => Step::Complete(d),
        }
    }

    /// Transform yielded values before returning them.
    #[allow(clippy::type_complexity)]
    fn map_yield<O2, F>(
        self,
        mut f: F,
    ) -> Step<(O2, MapYield<Self::Next, F, I, O>), <Self::Next as Sans<I, O>>::Done>
    where
        Self: Sized,
        F: FnMut(O) -> O2,
    {
        match self.init() {
            Step::Yielded((o, next)) => {
                let mapped_o = f(o);
                Step::Yielded((mapped_o, map_yield(f, next)))
            }
            Step::Complete(d) => Step::Complete(d),
        }
    }

    /// Transform the final result when completing.
    fn map_done<D2, F>(self, mut f: F) -> Step<(O, MapDone<Self::Next, F>), D2>
    where
        Self: Sized,
        F: FnMut(<Self::Next as Sans<I, O>>::Done) -> D2,
    {
        match self.init() {
            Step::Yielded((o, next)) => Step::Yielded((o, map_done(f, next))),
            Step::Complete(d) => Step::Complete(f(d)),
        }
    }
}

impl<I, O, S> InitSans<I, O> for (O, S)
where
    S: Sans<I, O>,
{
    type Next = S;
    fn init(self) -> Step<(O, S), S::Done> {
        Step::Yielded(self)
    }
}

impl<I, O, S> InitSans<I, O> for Step<(O, S), S::Done>
where
    S: Sans<I, O>,
{
    type Next = S;
    fn init(self) -> Step<(O, S), S::Done> {
        self
    }
}

impl<I, O, L, R> InitSans<I, O> for either::Either<L, R>
where
    L: InitSans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O, Done = <L::Next as Sans<I, O>>::Done>,
{
    type Next = either::Either<L::Next, R::Next>;
    fn init(self) -> Step<(O, Self::Next), <Self::Next as Sans<I, O>>::Done> {
        match self {
            either::Either::Left(l) => match l.init() {
                Step::Yielded((o, next_l)) => Step::Yielded((o, either::Either::Left(next_l))),
                Step::Complete(resume) => Step::Complete(resume),
            },
            either::Either::Right(r) => match r.init() {
                Step::Yielded((o, next_r)) => Step::Yielded((o, either::Either::Right(next_r))),
                Step::Complete(resume) => Step::Complete(resume),
            },
        }
    }
}

/// Chain an `InitSans` stage with a continuation.
///
/// Allows connecting stages that have initial yields with regular continuations.
pub fn init_chain<I, O, L, R>(first: (O, L), r: R) -> (O, Chain<L, R>)
where
    L: Sans<I, O, Done = I>,
    R: Sans<I, O>,
{
    (first.0, chain(first.1, r))
}

/// Yield an initial value, then apply a function once.
///
/// Combines immediate output with single function application.
pub fn init_once<I, O, F: FnOnce(I) -> O>(o: O, f: F) -> (O, Once<F>) {
    (o, once(f))
}

/// Yield an initial value, then apply a function indefinitely.
///
/// Useful for generators that need to emit a seed value before starting their loop.
pub fn init_repeat<I, O, F: FnMut(I) -> O>(o: O, f: F) -> (O, Repeat<F>) {
    (o, repeat(f))
}

/// Yield an initial value, then create a continuation from a closure.
///
/// ```rust
/// use cont::*;
///
/// let mut counter = 0;
/// let (initial, mut stage) = init_from_fn(42, move |x: i32| {
///     counter += 1;
///     if counter < 3 { Step::Yielded(x * counter) } else { Step::Complete(x + counter) }
/// });
/// assert_eq!(initial, 42);
/// assert_eq!(stage.next(10).unwrap_yielded(), 10);
/// assert_eq!(stage.next(10).unwrap_yielded(), 20);
/// assert_eq!(stage.next(10).unwrap_complete(), 13);
/// ```
pub fn init_from_fn<I, O, D, F>(initial: O, f: F) -> (O, FromFn<F>)
where
    F: FnMut(I) -> Step<O, D>,
{
    (initial, from_fn(f))
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

    impl Sans<&'static str, &'static str> for ImmediateFirstDone {
        type Done = &'static str;

        fn next(&mut self, input: &'static str) -> Step<&'static str, Self::Done> {
            Step::Complete(input)
        }
    }

    impl InitSans<&'static str, &'static str> for ImmediateFirstDone {
        type Next = Self;

        fn init(
            self,
        ) -> Step<(&'static str, Self::Next), <Self::Next as Sans<&'static str, &'static str>>::Done>
        {
            Step::Complete("left-done")
        }
    }

    #[test]
    fn test_simple_addition() {
        let mut prev = 1;
        let fib = init_repeat(1, move |n: u128| {
            let next = prev + n;
            prev = next;
            next
        });

        let (_, mut next) = fib.init().unwrap_yielded();
        for i in 1..11 {
            let cur = next.next(1).unwrap_yielded();
            assert_eq!(i + 1, cur);
        }
    }

    #[test]
    fn test_simple_divider() {
        let mut start = 101323012313805546028676730784521326u128;
        let divider = init_repeat(start, |divisor: u128| {
            start /= divisor;
            start
        });

        assert_eq!(size_of_val(&divider), 32);
        let (mut cur, mut next) = divider.init().unwrap_yielded();
        for i in 2..20 {
            let next_cur = next.next(i).unwrap_yielded();
            assert_eq!(cur / i, next_cur);
            cur = next_cur;
        }
    }

    #[test]
    fn test_chain_once_into_repeat() {
        let initializer = init_once(10_u32, |input: u32| input + 5);
        let mut multiplier = 2_u32;
        let repeater = repeat(move |input: u32| {
            let output = input * multiplier;
            multiplier += 1;
            output
        });

        let (first_yield, mut stage) = initializer.chain(repeater).init().unwrap_yielded();
        assert_eq!(10, first_yield);
        assert_eq!(13, stage.next(8).unwrap_yielded());
        assert_eq!(16, stage.next(8).unwrap_yielded());
        assert_eq!(24, stage.next(8).unwrap_yielded());
        assert_eq!(32, stage.next(8).unwrap_yielded());
    }

    #[test]
    fn test_map_input_and_map_yield_pipeline() {
        let mut total = 0_i64;
        let (initial_total, mut stage) = init_repeat(0_i64, move |delta: i64| {
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
        .unwrap_yielded()
        .map_yield(|value: i64| format!("total={value}"))
        .unwrap_yielded();

        assert_eq!("total=0", initial_total);
        assert_eq!("total=5", stage.next("add 5").unwrap_yielded());
        assert_eq!("total=2", stage.next("sub 3").unwrap_yielded());
        assert_eq!("total=7", stage.next("add 5").unwrap_yielded());
    }

    #[test]
    fn test_chain_and_map_done_resume_flow() {
        let initializer = init_once(42_u32, |input: u32| input + 1);
        let finisher = once(|input: u32| input * 3);

        let first = initializer.chain(finisher);
        let (first_value, mut stage) = (first
            .map_yield(|resume: u32| (resume + 7) as i32)
            .map_done(|done: u32| done as i32 * 3))
        .unwrap_yielded();

        assert_eq!(49, first_value);
        assert_eq!(18, stage.next(10).unwrap_yielded());
        assert_eq!(37, stage.next(10).unwrap_yielded());
        assert_eq!(30i32, stage.next(10).unwrap_complete());
    }

    #[test]
    fn test_either_first_right_branch_selected() {
        let stage: either::Either<(i32, Repeat<fn(i32) -> i32>), (i32, Repeat<fn(i32) -> i32>)> =
            either::Either::Right(init_repeat(2_i32, add_three));

        let (first_value, mut next_stage) = stage.init().unwrap_yielded();
        assert_eq!(2, first_value);
        assert_eq!(5, next_stage.next(2).unwrap_yielded());
        assert_eq!(6, next_stage.next(3).unwrap_yielded());
    }

    #[test]
    fn test_either_first_left_done_returns_resume() {
        let stage: either::Either<ImmediateFirstDone, ImmediateFirstDone> =
            either::Either::Left(ImmediateFirstDone);

        let resume = stage.init().unwrap_complete();
        assert_eq!("left-done", resume);
    }

    #[test]
    fn test_first_ext_map_input_yield_done() {
        let initializer = init_once(5_u32, |input: u32| input + 2);
        let finisher = once(|value: u32| value * 2);

        let (first_value, mut rest) = initializer
            .chain(finisher)
            .map_input(|text: &str| text.parse::<u32>().expect("number"))
            .unwrap_yielded()
            .map_yield(|value: u32| format!("value={value}"))
            .unwrap_yielded()
            .map_done(|resume: u32| format!("done={resume}"))
            .unwrap_yielded();
        assert_eq!("value=5", first_value);
        assert_eq!("value=9", rest.next("7").unwrap_yielded());
        assert_eq!("value=16", rest.next("8").unwrap_yielded());
        assert_eq!("done=9", rest.next("9").unwrap_complete());
    }
}
