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
    type Done = S::Done;
    fn next(&mut self, input: I1) -> Step<O, Self::Done> {
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
    type Done = S::Done;
    fn next(&mut self, input: I) -> Step<O2, Self::Done> {
        match self.stage.next(input) {
            Step::Yielded(o1) => Step::Yielded((self.f)(o1)),
            Step::Complete(a) => Step::Complete(a),
        }
    }
}

/// Transforms the final result from the wrapped stage.
///
/// Applied only when the computation completes, not to intermediate yields.
pub struct MapDone<S, F> {
    f: F,
    stage: S,
}

/// Create a continuation that transforms the final result from the wrapped stage.
pub fn map_done<S, F>(f: F, stage: S) -> MapDone<S, F> {
    MapDone { f, stage }
}

impl<I, O, D1, D2, S, F> Sans<I, O> for MapDone<S, F>
where
    S: Sans<I, O, Done = D1>,
    F: FnMut(D1) -> D2,
{
    type Done = D2;
    fn next(&mut self, input: I) -> Step<O, Self::Done> {
        match self.stage.next(input) {
            Step::Yielded(o) => Step::Yielded(o),
            Step::Complete(r1) => Step::Complete((self.f)(r1)),
        }
    }
}
