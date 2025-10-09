use crate::{InitSans, Sans, step::Step};

/// A continuation that runs one stage to completion, then uses its return value
/// to create and run a second stage.
///
/// This is similar to a monadic bind operation. The first stage runs until it
/// completes, then its return value is passed to a function that produces the
/// second stage (which must implement [`InitSans`]).
///
/// Created via the [`and_then`] function.
///
/// # Type Parameters
///
/// * `S1` - The type of the first stage
/// * `S2` - The type of the second stage's continuation (after initialization)
/// * `F` - The function type that creates the second stage from the first's return value
pub struct AndThen<S1, S2, F> {
    state: AndThenState<S1, S2, F>,
}

impl<I, O, L, R, F> Sans<I, O> for AndThen<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    type Return = <R::Next as Sans<I, O>>::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        self.state.next(input)
    }
}

enum AndThenState<S1, S2, F> {
    OnFirst(S1, Option<F>),
    OnSecond(S2),
}

impl<I, O, L, R, F> Sans<I, O> for AndThenState<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    type Return = <R::Next as Sans<I, O>>::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self {
            AndThenState::OnFirst(l, f) => match l.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(a) => {
                    let r = f.take().expect("AndThen::can only be used once")(a);
                    match r.init() {
                        Step::Yielded((o, next_r)) => {
                            *self = AndThenState::OnSecond(next_r);
                            Step::Yielded(o)
                        }
                        Step::Complete(d) => Step::Complete(d),
                    }
                }
            },
            AndThenState::OnSecond(r) => r.next(input),
        }
    }
}

/// Chains two stages where the second stage is created from the first stage's return value.
///
/// This is a monadic bind operation for continuations. The first stage runs to completion,
/// then its return value is passed to a function `f` that creates the second stage.
///
/// **Important:** The function `f` must return an [`InitSans`], not just a [`Sans`]. Use the
/// [`init()`](crate::build::init) helper to wrap a `Sans` with an initial output:
///
/// ```rust
/// use cont::prelude::*;
///
/// // Using init() makes the syntax cleaner
/// let mut stage = once(|x: i32| x * 2)
///     .and_then(|val| init(val * 10, repeat(move |x| x + val)));
/// ```
///
/// Alternatively, you can return a tuple `(initial_output, continuation)` or use
/// [`Step::Complete`] for immediate completion.
///
/// # Arguments
///
/// * `l` - The first stage to run
/// * `f` - A function that takes the first stage's return value and produces the second stage
///
/// # Returns
///
/// An [`AndThen`] continuation that runs both stages in sequence.
///
/// # Examples
///
/// ```
/// use cont::prelude::*;
/// use cont::compose::and_then;
///
/// // First stage yields once, then completes with a return value
/// // Second stage uses that return value to configure its behavior
/// let mut stage = and_then(
///     once(|x: i32| x * 2),  // yields x*2, returns next input
///     |return_val| init(return_val * 10, repeat(move |y: i32| y + return_val)),
/// );
///
/// // First stage yields 5 * 2 = 10
/// assert_eq!(stage.next(5).unwrap_yielded(), 10);
///
/// // First stage completes with return value = 7
/// // Second stage initializes with (7*10, ...) and yields 70
/// assert_eq!(stage.next(7).unwrap_yielded(), 70);
///
/// // Second stage continues: 3 + 7 = 10
/// assert_eq!(stage.next(3).unwrap_yielded(), 10);
/// ```
pub fn and_then<I, O, L, R, F>(l: L, f: F) -> AndThen<L, R::Next, F>
where
    L: Sans<I, O>,
    R: InitSans<I, O>,
    R::Next: Sans<I, O>,
    F: FnOnce(L::Return) -> R,
{
    AndThen {
        state: AndThenState::OnFirst(l, Some(f)),
    }
}

/// Run the first continuation to completion, then feed its result to the second.
///
/// The first stage's `Done` value becomes the input to the second stage.
/// Both stages must yield the same type.
pub fn chain<I, O, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Sans<I, O, Return = I>,
    R: Sans<I, O>,
{
    Chain(Some(l), r)
}

/// Create a chain from an InitSans stage and a continuation.
///
/// This is used when chaining an initial stage (that yields immediately) with a continuation.
pub fn init_chain<I, O, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: InitSans<I, O>,
    R: Sans<I, O>,
    L::Next: Sans<I, O, Return = I>,
{
    Chain(Some(l), r)
}

/// Chains two stages sequentially.
///
/// Created via `chain()` or `first_chain()`. The first stage is dropped from memory
/// once it completes to free resources.
pub struct Chain<S1, S2>(Option<S1>, S2);

impl<I, O, L, R> Sans<I, O> for Chain<L, R>
where
    L: Sans<I, O, Return = I>,
    R: Sans<I, O>,
{
    type Return = R::Return;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
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

impl<I, O, L, R> InitSans<I, O> for Chain<L, R>
where
    L: InitSans<I, O>,
    R: Sans<I, O>,
    L::Next: Sans<I, O, Return = I>,
{
    type Next = either::Either<Chain<L::Next, R>, R>;

    fn init(mut self) -> Step<(O, Self::Next), R::Return> {
        match self.0.take().expect("Chain left side must be Some").init() {
            Step::Yielded((o, next)) => {
                Step::Yielded((o, either::Either::Left(Chain(Some(next), self.1))))
            }
            Step::Complete(d) => {
                match self.1.next(d) {
                    Step::Yielded(o) => {
                        Step::Yielded((o, either::Either::Right(self.1)))
                    }
                    Step::Complete(r) => Step::Complete(r),
                }
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::{once, repeat};

    #[test]
    fn test_chain_switches_to_second_stage_after_first_done() {
        let mut stage = chain(once(|val: u32| val + 1), repeat(|val: u32| val * 2));

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
    fn test_and_then_basic() {
        // First stage yields once then completes with a computed value
        // and_then uses the RETURN value of first stage to create second stage
        let mut stage = and_then(
            once(|x: i32| x * 2),  // yields x*2, then completes with next input
            |return_val| (return_val * 10, repeat(move |y: i32| y + return_val)),
        );

        // First: 5 * 2 = 10 (yielded)
        assert_eq!(stage.next(5).unwrap_yielded(), 10);
        // Second: once completes with return value = 7
        // and_then creates second stage with return_val=7
        // Second stage initializes: (7*10, ...) = (70, ...)
        // Yields 70
        assert_eq!(stage.next(7).unwrap_yielded(), 70);
        // Second stage continues: 3 + 7 = 10
        assert_eq!(stage.next(3).unwrap_yielded(), 10);
        // 5 + 7 = 12
        assert_eq!(stage.next(5).unwrap_yielded(), 12);
    }

    #[test]
    fn test_and_then_first_stage_yields_multiple() {
        // First stage yields twice before completing
        use crate::build::from_fn;
        let mut count = 0;
        let first = from_fn(move |x: i32| {
            count += 1;
            if count <= 2 {
                Step::Yielded(x * count)
            } else {
                Step::Complete(count)
            }
        });

        let mut stage = and_then(first, |final_count| (final_count * 100, once(move |x: i32| x + final_count)));

        // First yields
        assert_eq!(stage.next(5).unwrap_yielded(), 5);  // 5 * 1
        assert_eq!(stage.next(5).unwrap_yielded(), 10); // 5 * 2
        // Now first completes with count=3, second stage initializes with (300, ...)
        assert_eq!(stage.next(0).unwrap_yielded(), 300); // Initial yield 3 * 100
        // Second stage continues: 10 + 3 = 13
        assert_eq!(stage.next(10).unwrap_yielded(), 13); // 10 + 3
        // Second stage (once) completes
        assert_eq!(stage.next(20).unwrap_complete(), 20);
    }

    #[test]
    fn test_and_then_with_init_sans() {
        // Second stage has initial yield
        let mut stage = and_then(
            once(|x: i32| x + 1),
            |result| (result * 10, repeat(move |y: i32| y + result)),
        );

        // First stage: 5 + 1 = 6 (yielded)
        assert_eq!(stage.next(5).unwrap_yielded(), 6);
        // First stage completes with result = 8
        // Second stage initializes with (8 * 10, ...) = (80, ...)
        // Yields the initial value 80
        assert_eq!(stage.next(8).unwrap_yielded(), 80);
        // Now the repeat continues: y + result = 3 + 8 = 11
        assert_eq!(stage.next(3).unwrap_yielded(), 11);
    }

    #[test]
    fn test_and_then_completes_immediately() {
        // First stage completes on first input, second stage yields once then completes
        let mut stage = and_then(
            once(|x: i32| x * 2),
            |val| (val + 100, once(move |x: i32| x + val)),
        );

        // First: 5 * 2 = 10 (yielded)
        assert_eq!(stage.next(5).unwrap_yielded(), 10);
        // First completes with val = 12
        // Second initializes with (12 + 100, once(...)) = (112, ...)
        // Yields 112
        assert_eq!(stage.next(12).unwrap_yielded(), 112);
        // Second continues: 20 + 12 = 32
        assert_eq!(stage.next(20).unwrap_yielded(), 32);
        // Second completes with 7
        assert_eq!(stage.next(7).unwrap_complete(), 7);
    }
}
