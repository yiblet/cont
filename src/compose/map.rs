use crate::{Sans, step::Step};

/// Transforms input before passing it to the wrapped stage.
///
/// Useful for adapting between different input types or preprocessing data.
pub struct MapInput<S, F> {
    f: F,
    stage: S,
}

/// Create a continuation that transforms input before passing it to the wrapped stage.
pub fn map_input<S, F>(f: F, stage: S) -> MapInput<S, F> {
    MapInput { f, stage }
}

impl<I1, I2, O, S, F> Sans<I1, O> for MapInput<S, F>
where
    S: Sans<I2, O>,
    F: FnMut(I1) -> I2,
{
    type Return = S::Return;
    fn next(&mut self, input: I1) -> Step<O, Self::Return> {
        let i2 = (self.f)(input);
        self.stage.next(i2)
    }
}

/// Transforms yielded values from the wrapped stage.
///
/// Allows converting or formatting output without changing the underlying computation.
pub struct MapYield<S, F, I, O1> {
    f: F,
    stage: S,
    _phantom: std::marker::PhantomData<(I, O1)>,
}

/// Create a continuation that transforms yielded values from the wrapped stage.
pub fn map_yield<I, O1, O2, S, F>(f: F, stage: S) -> MapYield<S, F, I, O1>
where
    S: Sans<I, O1>,
    F: FnMut(O1) -> O2,
{
    MapYield { f, stage, _phantom: std::marker::PhantomData }
}

impl<I, O1, O2, S, F> Sans<I, O2> for MapYield<S, F, I, O1>
where
    S: Sans<I, O1>,
    F: FnMut(O1) -> O2,
{
    type Return = S::Return;
    fn next(&mut self, input: I) -> Step<O2, Self::Return> {
        match self.stage.next(input) {
            Step::Yielded(o1) => Step::Yielded((self.f)(o1)),
            Step::Complete(a) => Step::Complete(a),
        }
    }
}

/// Transforms the final result from the wrapped stage.
///
/// Applied only when the computation completes, not to intermediate yields.
pub struct MapReturn<S, F> {
    f: F,
    stage: S,
}

/// Create a continuation that transforms the final result from the wrapped stage.
pub fn map_return<S, F>(f: F, stage: S) -> MapReturn<S, F> {
    MapReturn { f, stage }
}

impl<I, O, D1, D2, S, F> Sans<I, O> for MapReturn<S, F>
where
    S: Sans<I, O, Return = D1>,
    F: FnMut(D1) -> D2,
{
    type Return = D2;
    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self.stage.next(input) {
            Step::Yielded(o) => Step::Yielded(o),
            Step::Complete(r1) => Step::Complete((self.f)(r1)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::repeat;
    use crate::InitSans;

    #[test]
    fn test_map_input_and_map_yield_pipeline() {
        let mut total = 0_i64;
        let init_stage = (0_i64, repeat(move |delta: i64| {
            total += delta;
            total
        }))
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

        let (initial_total, mut stage) = init_stage.init().unwrap_yielded();

        assert_eq!("total=0", initial_total);
        assert_eq!("total=5", stage.next("add 5").unwrap_yielded());
        assert_eq!("total=2", stage.next("sub 3").unwrap_yielded());
        assert_eq!("total=7", stage.next("add 5").unwrap_yielded());
    }
}
