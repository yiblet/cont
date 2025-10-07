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
    f: F,
    stage: S,
}

/// Create a continuation that transforms yielded values from the wrapped stage.
pub fn map_yield<S, F>(f: F, stage: S) -> MapYield<S, F> {
    MapYield { f, stage }
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
    f: F,
    stage: S,
}

/// Create a continuation that transforms the final result from the wrapped stage.
pub fn map_done<S, F>(f: F, stage: S) -> MapDone<S, F> {
    MapDone { f, stage }
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
