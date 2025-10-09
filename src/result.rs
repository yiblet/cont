//! Result combinators for error handling in coroutines.
//!
//! This module provides adapters and extension traits for working with [`Result`] types
//! in coroutine pipelines, enabling composable error handling patterns.
//!
//! # Core Combinators
//!
//! - [`short_circuit`] - Short-circuits on the first `Err` in yielded values
//! - [`ok_map`] - Maps `Ok` return values through a function that produces an [`InitSans`]
//! - [`ok_and_then`] - Chains through a function that produces a fallible [`InitSans`]
//! - [`ok_chain`] - Chains to another stage only if the first returns `Ok`
//! - [`flatten`] - Flattens nested `Result<Result<T, E>, E>` types
//!
//! # Extension Traits
//!
//! The [`TrySans`] and [`TryInitSans`] traits provide method syntax for these combinators,
//! enabling fluent error handling chains.
//!
//! # Examples
//!
//! ```
//! use sans::prelude::*;
//! use sans::result::{short_circuit, TrySans};
//!
//! // Short-circuit on errors
//! let stage = repeat(|x: i32| {
//!     if x < 0 { Err("negative") } else { Ok(x * 2) }
//! });
//! let mut sc = short_circuit(stage);
//!
//! assert_eq!(sc.next(5).unwrap_yielded(), 10);
//! assert_eq!(sc.next(-1).unwrap_complete(), Err("negative"));
//! ```
use crate::{InitSans, Sans, step::Step};

/// Short-circuits on the first `Err` in a yielded `Result`.
///
/// Converts `Sans<I, Result<O, E>, Return = P>` to `Sans<I, O, Return = Result<P, E>>`.
/// If any yield is `Err(e)`, immediately completes with `Err(e)`.
/// Otherwise yields unwrapped `Ok` values and completes with `Ok(P)`.
pub struct ShortCircuit<S, E> {
    stage: S,
    _phantom: std::marker::PhantomData<E>,
}

/// Create a coroutine that short-circuits on the first yielded `Err`.
///
/// # Examples
///
/// ```
/// use sans::prelude::*;
/// use sans::result::short_circuit;
///
/// let stage = repeat(|x: i32| {
///     if x < 0 { Err("negative") } else { Ok(x * 2) }
/// });
/// let mut sc = short_circuit(stage);
///
/// assert_eq!(sc.next(5).unwrap_yielded(), 10);
/// assert_eq!(sc.next(-1).unwrap_complete(), Err("negative"));
/// ```
pub fn short_circuit<S, E>(stage: S) -> ShortCircuit<S, E> {
    ShortCircuit {
        stage,
        _phantom: std::marker::PhantomData,
    }
}

/// Create a ShortCircuit from an InitSans stage.
///
/// This is used when applying short-circuit to a stage that yields immediately.
pub fn init_short_circuit<I, O, E, S>(stage: S) -> ShortCircuit<S, E>
where
    S: InitSans<I, Result<O, E>>,
{
    ShortCircuit {
        stage,
        _phantom: std::marker::PhantomData,
    }
}

impl<I, O, E, S> Sans<I, O> for ShortCircuit<S, E>
where
    S: Sans<I, Result<O, E>>,
{
    type Return = Result<S::Return, E>;

    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self.stage.next(input) {
            Step::Yielded(Ok(o)) => Step::Yielded(o),
            Step::Yielded(Err(e)) => Step::Complete(Err(e)),
            Step::Complete(p) => Step::Complete(Ok(p)),
        }
    }
}

impl<I, O, E, S> InitSans<I, O> for ShortCircuit<S, E>
where
    S: InitSans<I, Result<O, E>>,
{
    type Next = ShortCircuit<S::Next, E>;

    fn init(self) -> Step<(O, Self::Next), Result<<S::Next as Sans<I, Result<O, E>>>::Return, E>> {
        match self.stage.init() {
            Step::Yielded((Ok(o), next)) => Step::Yielded((
                o,
                ShortCircuit {
                    stage: next,
                    _phantom: std::marker::PhantomData,
                },
            )),
            Step::Yielded((Err(e), _)) => Step::Complete(Err(e)),
            Step::Complete(p) => Step::Complete(Ok(p)),
        }
    }
}

/// Maps `Ok` values through a function that produces an `InitSans`.
///
/// If the stage completes with `Err`, propagates the error.
/// If it completes with `Ok(p)`, calls `f(p)` and wraps the result in `Ok`.
pub struct OkMap<S, T, F> {
    state: OkMapState<S, T, F>,
}

enum OkMapState<S, T, F> {
    OnFirst(S, Option<F>),
    OnSecond(T),
}

/// Create a coroutine that maps `Ok` return values through a function.
///
/// # Examples
///
/// ```
/// use sans::prelude::*;
/// use sans::result::ok_map;
/// use sans::build::from_fn;
/// use sans::Step;
///
/// let mut called = false;
/// let stage = from_fn(move |x: i32| -> Step<i32, Result<i32, String>> {
///     if !called {
///         called = true;
///         Step::Yielded(x * 2)
///     } else if x > 0 {
///         Step::Complete(Ok(x))
///     } else {
///         Step::Complete(Err("non-positive".to_string()))
///     }
/// });
///
/// let mut mapped = ok_map(stage, |val| init(val, repeat(move |x: i32| x + val)));
///
/// // First input: 5 -> yields 10
/// assert_eq!(mapped.next(5).unwrap_yielded(), 10);
/// // Second input: completes with Ok(3), starts second stage with val=3
/// assert_eq!(mapped.next(3).unwrap_yielded(), 3);
/// // Third input: second stage continues 7 + 3 = 10
/// assert_eq!(mapped.next(7).unwrap_yielded(), 10);
/// ```
pub fn ok_map<I, O, P, E, S, T, F>(stage: S, f: F) -> OkMap<S, T::Next, F>
where
    S: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O>,
    F: FnOnce(P) -> T,
{
    OkMap {
        state: OkMapState::OnFirst(stage, Some(f)),
    }
}

/// Create an OkMap from an InitSans stage.
///
/// This is used when applying ok_map to a stage that yields immediately.
pub fn init_ok_map<I, O, P, E, S, T, F>(stage: S, f: F) -> OkMap<S, T::Next, F>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O>,
    F: FnOnce(P) -> T,
{
    OkMap {
        state: OkMapState::OnFirst(stage, Some(f)),
    }
}

impl<I, O, P, E, S, T, F> Sans<I, O> for OkMap<S, T::Next, F>
where
    S: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O>,
    F: FnOnce(P) -> T,
{
    type Return = Result<<T::Next as Sans<I, O>>::Return, E>;

    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match &mut self.state {
            OkMapState::OnSecond(next) => next.next(input).map_complete(Ok),
            OkMapState::OnFirst(stage, f) => match stage.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(Err(e)) => Step::Complete(Err(e)),
                Step::Complete(Ok(p)) => {
                    let f = f.take().expect("ok_map can only be used once");
                    let init_sans = f(p);
                    match init_sans.init() {
                        Step::Yielded((o, next)) => {
                            *self = OkMap {
                                state: OkMapState::OnSecond(next),
                            };
                            Step::Yielded(o)
                        }
                        Step::Complete(ret) => Step::Complete(Ok(ret)),
                    }
                }
            },
        }
    }
}

impl<I, O, P, E, S, T, F> InitSans<I, O> for OkMap<S, T::Next, F>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O>,
    F: FnOnce(P) -> T,
{
    type Next = OkMap<S::Next, T::Next, F>;

    fn init(self) -> Step<(O, Self::Next), Result<<T::Next as Sans<I, O>>::Return, E>> {
        let OkMapState::OnFirst(stage, f) = self.state else {
            unreachable!("OkMap::init called on OnSecond state")
        };

        match stage.init() {
            Step::Yielded((o, next)) => Step::Yielded((
                o,
                OkMap {
                    state: OkMapState::OnFirst(next, f),
                },
            )),
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
            Step::Complete(Ok(p)) => {
                let f = f.expect("f should be available");
                let init_sans = f(p);
                match init_sans.init() {
                    Step::Yielded((o, next)) => Step::Yielded((
                        o,
                        OkMap {
                            state: OkMapState::OnSecond(next),
                        },
                    )),
                    Step::Complete(ret) => Step::Complete(Ok(ret)),
                }
            }
        }
    }
}

/// Chains through a function that produces an `InitSans` with a `Result` return type.
///
/// If the stage completes with `Err`, propagates the error without calling `f`.
/// If it completes with `Ok(p)`, calls `f(p)` which itself can return `Result`.
pub struct OkAndThen<S, T, F> {
    state: OkAndThenState<S, T, F>,
}

enum OkAndThenState<S, T, F> {
    OnFirst(S, Option<F>),
    OnSecond(T),
}

/// Create a coroutine that chains `Ok` values through a fallible function.
///
/// # Examples
///
/// ```
/// use sans::prelude::*;
/// use sans::result::ok_and_then;
/// use sans::build::from_fn;
/// use sans::Step;
///
/// let mut first_called = false;
/// let stage = from_fn(move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
///     if !first_called {
///         first_called = true;
///         Step::Yielded(Ok(x * 2))
///     } else if x > 0 {
///         Step::Complete(Ok(x))
///     } else {
///         Step::Complete(Err("non-positive".to_string()))
///     }
/// });
///
/// let mut chained = ok_and_then(stage, move |val| {
///     let mut second_called = false;
///     init(Ok(val), from_fn(move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
///         if !second_called {
///             second_called = true;
///             if x > 100 { Step::Yielded(Err("too large".to_string())) } else { Step::Yielded(Ok(x + val)) }
///         } else {
///             Step::Complete(Ok(x))
///         }
///     }))
/// });
///
/// // First input: 5 -> yields Ok(10)
/// assert_eq!(chained.next(5).unwrap_yielded(), Ok(10));
/// // Second input: completes with Ok(3), starts second stage with val=3, yields Ok(3)
/// assert_eq!(chained.next(3).unwrap_yielded(), Ok(3));
/// // Third input: 7 -> yields Ok(7+3) = Ok(10)
/// assert_eq!(chained.next(7).unwrap_yielded(), Ok(10));
/// ```
pub fn ok_and_then<I, O, P, Q, E, S, T, F>(stage: S, f: F) -> OkAndThen<S, T::Next, F>
where
    S: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O, Return = Result<Q, E>>,
    F: FnOnce(P) -> T,
{
    OkAndThen {
        state: OkAndThenState::OnFirst(stage, Some(f)),
    }
}

/// Create an OkAndThen from an InitSans stage.
///
/// This is used when applying ok_and_then to a stage that yields immediately.
pub fn init_ok_and_then<I, O, P, Q, E, S, T, F>(stage: S, f: F) -> OkAndThen<S, T::Next, F>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O, Return = Result<Q, E>>,
    F: FnOnce(P) -> T,
{
    OkAndThen {
        state: OkAndThenState::OnFirst(stage, Some(f)),
    }
}

impl<I, O, P, Q, E, S, T, F> Sans<I, O> for OkAndThen<S, T::Next, F>
where
    S: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O, Return = Result<Q, E>>,
    F: FnOnce(P) -> T,
{
    type Return = Result<Q, E>;

    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match &mut self.state {
            OkAndThenState::OnSecond(next) => next.next(input),
            OkAndThenState::OnFirst(stage, f) => match stage.next(input) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(Err(e)) => Step::Complete(Err(e)),
                Step::Complete(Ok(p)) => {
                    let f = f.take().expect("ok_and_then can only be used once");
                    let init_sans = f(p);
                    match init_sans.init() {
                        Step::Yielded((o, next)) => {
                            *self = OkAndThen {
                                state: OkAndThenState::OnSecond(next),
                            };
                            Step::Yielded(o)
                        }
                        Step::Complete(ret) => Step::Complete(ret),
                    }
                }
            },
        }
    }
}

impl<I, O, P, Q, E, S, T, F> InitSans<I, O> for OkAndThen<S, T::Next, F>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<P, E>>,
    T: InitSans<I, O>,
    T::Next: Sans<I, O, Return = Result<Q, E>>,
    F: FnOnce(P) -> T,
{
    type Next = OkAndThen<S::Next, T::Next, F>;

    fn init(self) -> Step<(O, Self::Next), Result<Q, E>> {
        let OkAndThenState::OnFirst(stage, f) = self.state else {
            unreachable!("OkAndThen::init called on OnSecond state")
        };

        match stage.init() {
            Step::Yielded((o, next)) => Step::Yielded((
                o,
                OkAndThen {
                    state: OkAndThenState::OnFirst(next, f),
                },
            )),
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
            Step::Complete(Ok(p)) => {
                let f = f.expect("f should be available");
                let init_sans = f(p);
                match init_sans.init() {
                    Step::Yielded((o, next)) => Step::Yielded((
                        o,
                        OkAndThen {
                            state: OkAndThenState::OnSecond(next),
                        },
                    )),
                    Step::Complete(ret) => Step::Complete(ret),
                }
            }
        }
    }
}

/// Chains to another stage only if the first returns `Ok`.
///
/// Converts the Ok value to the input type for the next stage.
pub struct OkChain<S, R> {
    stage: Option<S>,
    next: R,
}

/// Create a coroutine that chains to another stage on `Ok`.
///
/// # Examples
///
/// ```
/// use sans::prelude::*;
/// use sans::result::ok_chain;
/// use sans::build::from_fn;
/// use sans::Step;
///
/// let mut called = false;
/// let first = from_fn(move |x: i32| -> Step<i32, Result<i32, String>> {
///     if !called {
///         called = true;
///         Step::Yielded(x * 2)
///     } else if x > 0 {
///         Step::Complete(Ok(x))
///     } else {
///         Step::Complete(Err("non-positive".to_string()))
///     }
/// });
/// let second = repeat(|x: i32| x + 1);
///
/// let mut chained = ok_chain(first, second);
///
/// // First input: 5 -> yields 10
/// assert_eq!(chained.next(5).unwrap_yielded(), 10);
/// // Second input: completes with Ok(3), chains with 3
/// assert_eq!(chained.next(3).unwrap_yielded(), 4);
/// // Now in second stage
/// assert_eq!(chained.next(10).unwrap_yielded(), 11);
/// ```
pub fn ok_chain<I, O, E, S, R>(stage: S, next: R) -> OkChain<S, R>
where
    S: Sans<I, O, Return = Result<I, E>>,
    R: Sans<I, O>,
{
    OkChain {
        stage: Some(stage),
        next,
    }
}

/// Create an OkChain from an InitSans stage.
///
/// This is used when applying ok_chain to a stage that yields immediately.
pub fn init_ok_chain<I, O, E, S, R>(stage: S, next: R) -> OkChain<S, R>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<I, E>>,
    R: Sans<I, O>,
{
    OkChain {
        stage: Some(stage),
        next,
    }
}

impl<I, O, E, S, R> Sans<I, O> for OkChain<S, R>
where
    S: Sans<I, O, Return = Result<I, E>>,
    R: Sans<I, O>,
{
    type Return = Result<R::Return, E>;

    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        if self.stage.is_none() {
            return self.next.next(input).map_complete(Ok);
        }

        let mut stage = self.stage.take().expect("OkChain stage already consumed");
        match stage.next(input) {
            Step::Yielded(o) => {
                self.stage = Some(stage);
                Step::Yielded(o)
            }
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
            Step::Complete(Ok(i)) => match self.next.next(i) {
                Step::Yielded(o) => Step::Yielded(o),
                Step::Complete(ret) => Step::Complete(Ok(ret)),
            },
        }
    }
}

impl<I, O, E, S, R> InitSans<I, O> for OkChain<S, R>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<I, E>>,
    R: Sans<I, O>,
{
    type Next = OkChain<S::Next, R>;

    fn init(mut self) -> Step<(O, Self::Next), Result<R::Return, E>> {
        match self
            .stage
            .take()
            .expect("OkChain stage must be Some")
            .init()
        {
            Step::Yielded((o, next)) => Step::Yielded((
                o,
                OkChain {
                    stage: Some(next),
                    next: self.next,
                },
            )),
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
            Step::Complete(Ok(i)) => match self.next.next(i) {
                Step::Yielded(o) => Step::Yielded((
                    o,
                    OkChain {
                        stage: None,
                        next: self.next,
                    },
                )),
                Step::Complete(ret) => Step::Complete(Ok(ret)),
            },
        }
    }
}

/// Flattens nested `Result` types in the return value.
///
/// Converts `Result<Result<T, E>, E>` to `Result<T, E>`.
pub struct Flatten<S> {
    stage: S,
}

/// Create a coroutine that flattens nested `Result` types.
///
/// # Examples
///
/// ```
/// use sans::prelude::*;
/// use sans::result::flatten;
/// use sans::build::from_fn;
/// use sans::Step;
///
/// let mut called = false;
/// let stage = from_fn(move |x: i32| -> Step<Result<Result<i32, String>, String>, Result<Result<i32, String>, String>> {
///     if !called {
///         called = true;
///         if x > 0 {
///             if x < 100 { Step::Yielded(Ok(Ok(x * 2))) } else { Step::Yielded(Ok(Err("too large".to_string()))) }
///         } else {
///             Step::Yielded(Err("non-positive".to_string()))
///         }
///     } else {
///         Step::Complete(Ok(Ok(x)))
///     }
/// });
///
/// let mut flattened = flatten(stage);
///
/// assert_eq!(flattened.next(5).unwrap_yielded(), Ok(Ok(10)));
/// // Second call completes with flattened result
/// assert_eq!(flattened.next(10).unwrap_complete(), Ok(10));
/// ```
pub fn flatten<S>(stage: S) -> Flatten<S> {
    Flatten { stage }
}

/// Create a Flatten from an InitSans stage.
///
/// This is used when applying flatten to a stage that yields immediately.
pub fn init_flatten<I, O, T, E, S>(stage: S) -> Flatten<S>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<Result<T, E>, E>>,
{
    Flatten { stage }
}

impl<I, O, T, E, S> Sans<I, O> for Flatten<S>
where
    S: Sans<I, O, Return = Result<Result<T, E>, E>>,
{
    type Return = Result<T, E>;

    fn next(&mut self, input: I) -> Step<O, Self::Return> {
        match self.stage.next(input) {
            Step::Yielded(o) => Step::Yielded(o),
            Step::Complete(Ok(Ok(t))) => Step::Complete(Ok(t)),
            Step::Complete(Ok(Err(e))) => Step::Complete(Err(e)),
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
        }
    }
}

impl<I, O, T, E, S> InitSans<I, O> for Flatten<S>
where
    S: InitSans<I, O>,
    S::Next: Sans<I, O, Return = Result<Result<T, E>, E>>,
{
    type Next = Flatten<S::Next>;

    fn init(self) -> Step<(O, Self::Next), Result<T, E>> {
        match self.stage.init() {
            Step::Yielded((o, next)) => Step::Yielded((o, Flatten { stage: next })),
            Step::Complete(Ok(Ok(t))) => Step::Complete(Ok(t)),
            Step::Complete(Ok(Err(e))) => Step::Complete(Err(e)),
            Step::Complete(Err(e)) => Step::Complete(Err(e)),
        }
    }
}

/// Extension trait for `Sans` that provides result combinator methods.
///
/// This trait is automatically implemented for all types that implement `Sans`.
pub trait TrySans<I, O>: Sized {
    /// Maps `Ok` return values through a function that produces an `InitSans`.
    fn ok_map<P, E, T, F>(self, f: F) -> OkMap<Self, T::Next, F>
    where
        Self: Sans<I, O, Return = Result<P, E>>,
        T: InitSans<I, O>,
        T::Next: Sans<I, O>,
        F: FnOnce(P) -> T,
    {
        ok_map(self, f)
    }

    /// Chains through a function that produces an `InitSans` with a `Result` return type.
    fn ok_and_then<P, Q, E, T, F>(self, f: F) -> OkAndThen<Self, T::Next, F>
    where
        Self: Sans<I, O, Return = Result<P, E>>,
        T: InitSans<I, O>,
        T::Next: Sans<I, O, Return = Result<Q, E>>,
        F: FnOnce(P) -> T,
    {
        ok_and_then(self, f)
    }

    /// Chains to another stage only if the first returns `Ok`.
    fn ok_chain<E, R>(self, next: R) -> OkChain<Self, R>
    where
        Self: Sans<I, O, Return = Result<I, E>>,
        R: Sans<I, O>,
    {
        ok_chain(self, next)
    }

    /// Flattens nested `Result` types in the return value.
    fn flatten<T, E>(self) -> Flatten<Self>
    where
        Self: Sans<I, O, Return = Result<Result<T, E>, E>>,
    {
        flatten(self)
    }
}

impl<I, O, S> TrySans<I, O> for S where S: Sans<I, O> {}

/// Extension trait for `InitSans` that provides result combinator methods.
///
/// This trait is automatically implemented for all types that implement `InitSans`.
pub trait TryInitSans<I, O>: InitSans<I, O> + Sized {
    /// Maps `Ok` return values through a function that produces an `InitSans`.
    fn ok_map<P, E, T, F>(self, f: F) -> OkMap<Self, T::Next, F>
    where
        Self: InitSans<I, O>,
        Self::Next: Sans<I, O, Return = Result<P, E>>,
        T: InitSans<I, O>,
        T::Next: Sans<I, O>,
        F: FnOnce(P) -> T,
    {
        init_ok_map(self, f)
    }

    /// Chains through a function that produces an `InitSans` with a `Result` return type.
    fn ok_and_then<P, Q, E, T, F>(self, f: F) -> OkAndThen<Self, T::Next, F>
    where
        Self: InitSans<I, O>,
        Self::Next: Sans<I, O, Return = Result<P, E>>,
        T: InitSans<I, O>,
        T::Next: Sans<I, O, Return = Result<Q, E>>,
        F: FnOnce(P) -> T,
    {
        init_ok_and_then(self, f)
    }

    /// Chains to another stage only if the first returns `Ok`.
    fn ok_chain<E, R>(self, next: R) -> OkChain<Self, R>
    where
        Self: InitSans<I, O>,
        Self::Next: Sans<I, O, Return = Result<I, E>>,
        R: Sans<I, O>,
    {
        init_ok_chain(self, next)
    }

    /// Flattens nested `Result` types in the return value.
    fn flatten<T, E>(self) -> Flatten<Self>
    where
        Self: InitSans<I, O>,
        Self::Next: Sans<I, O, Return = Result<Result<T, E>, E>>,
    {
        init_flatten(self)
    }
}

impl<I, O, S> TryInitSans<I, O> for S where S: InitSans<I, O> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::init;
    use crate::build::{once, repeat};

    #[test]
    fn test_short_circuit_propagates_ok_yields() {
        let stage = repeat(|x: i32| if x < 0 { Err("negative") } else { Ok(x * 2) });
        let mut sc = short_circuit(stage);

        assert_eq!(sc.next(5).unwrap_yielded(), 10);
        assert_eq!(sc.next(3).unwrap_yielded(), 6);
        assert_eq!(sc.next(10).unwrap_yielded(), 20);
    }

    #[test]
    fn test_short_circuit_stops_on_err() {
        let stage = repeat(|x: i32| if x < 0 { Err("negative") } else { Ok(x * 2) });
        let mut sc = short_circuit(stage);

        assert_eq!(sc.next(5).unwrap_yielded(), 10);
        assert_eq!(sc.next(-1).unwrap_complete(), Err("negative"));
    }

    #[test]
    fn test_short_circuit_completes_with_ok() {
        let stage = once(|x: i32| if x < 0 { Err("negative") } else { Ok(x * 2) });
        let mut sc = short_circuit(stage);

        assert_eq!(sc.next(5).unwrap_yielded(), 10);
        assert_eq!(sc.next(3).unwrap_complete(), Ok(3));
    }

    #[test]
    fn test_ok_map_propagates_err() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(move |x: i32| {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else if x > 0 {
                Step::Complete(Ok(x))
            } else {
                Step::Complete(Err("non-positive".to_string()))
            }
        });

        let mut mapped = ok_map(stage, |val| init(val, repeat(move |x: i32| x + val)));

        assert_eq!(mapped.next(5).unwrap_yielded(), 10);
        assert_eq!(
            mapped.next(-5).unwrap_complete(),
            Err("non-positive".to_string())
        );
    }

    #[test]
    fn test_ok_map_chains_on_ok() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(move |x: i32| -> Step<i32, Result<i32, String>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });

        let mut mapped = ok_map(stage, |val| init(val, repeat(move |x: i32| x + val)));

        assert_eq!(mapped.next(5).unwrap_yielded(), 10);
        assert_eq!(mapped.next(3).unwrap_yielded(), 3); // initial value from init
        assert_eq!(mapped.next(7).unwrap_yielded(), 10); // 3 + 7
    }

    #[test]
    fn test_ok_and_then_propagates_err_from_first() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(
            move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                if !called {
                    called = true;
                    Step::Yielded(Ok(x * 2))
                } else if x > 0 {
                    Step::Complete(Ok(x))
                } else {
                    Step::Complete(Err("non-positive".to_string()))
                }
            },
        );

        let mut chained = ok_and_then(stage, |val| {
            init(
                Ok(val),
                from_fn(
                    move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                        Step::Yielded(Ok(x + val))
                    },
                ),
            )
        });

        assert_eq!(chained.next(5).unwrap_yielded(), Ok(10));
        assert_eq!(
            chained.next(-5).unwrap_complete(),
            Err("non-positive".to_string())
        );
    }

    #[test]
    fn test_ok_and_then_chains_and_propagates_err_from_second() {
        use crate::build::from_fn;
        let mut first_called = false;
        let stage = from_fn(
            move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                if !first_called {
                    first_called = true;
                    Step::Yielded(Ok(x * 2))
                } else {
                    Step::Complete(Ok(x))
                }
            },
        );

        let mut chained = ok_and_then(stage, |val| {
            init(
                Ok(val),
                from_fn(
                    move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                        if x > 100 {
                            Step::Yielded(Err("too large".to_string()))
                        } else {
                            Step::Yielded(Ok(x + val))
                        }
                    },
                ),
            )
        });

        assert_eq!(chained.next(5).unwrap_yielded(), Ok(10));
        assert_eq!(chained.next(3).unwrap_yielded(), Ok(3));
        assert_eq!(chained.next(50).unwrap_yielded(), Ok(53));
        assert_eq!(
            chained.next(200).unwrap_yielded(),
            Err("too large".to_string())
        );
    }

    #[test]
    fn test_ok_and_then_both_ok() {
        use crate::build::from_fn;
        let mut first_called = false;
        let stage = from_fn(
            move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                if !first_called {
                    first_called = true;
                    Step::Yielded(Ok(x * 2))
                } else {
                    Step::Complete(Ok(x))
                }
            },
        );

        let mut chained = ok_and_then(stage, |val| {
            let mut second_called = false;
            init(
                Ok(val),
                from_fn(
                    move |x: i32| -> Step<Result<i32, String>, Result<i32, String>> {
                        if !second_called {
                            second_called = true;
                            Step::Yielded(Ok(x + val))
                        } else {
                            Step::Complete(Ok(x))
                        }
                    },
                ),
            )
        });

        assert_eq!(chained.next(5).unwrap_yielded(), Ok(10));
        assert_eq!(chained.next(3).unwrap_yielded(), Ok(3));
        assert_eq!(chained.next(7).unwrap_yielded(), Ok(10));
        assert_eq!(chained.next(5).unwrap_complete(), Ok(5));
    }

    #[test]
    fn test_ok_chain_propagates_err() {
        use crate::build::from_fn;
        let mut called = false;
        let first = from_fn(move |x: i32| {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else if x > 0 {
                Step::Complete(Ok(x))
            } else {
                Step::Complete(Err("non-positive".to_string()))
            }
        });
        let second = repeat(|x: i32| x + 1);

        let mut chained = ok_chain(first, second);

        assert_eq!(chained.next(5).unwrap_yielded(), 10);
        assert_eq!(
            chained.next(-5).unwrap_complete(),
            Err("non-positive".to_string())
        );
    }

    #[test]
    fn test_ok_chain_chains_on_ok() {
        use crate::build::from_fn;
        let mut called = false;
        let first = from_fn(move |x: i32| -> Step<i32, Result<i32, String>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });
        let second = repeat(|x: i32| x + 1);

        let mut chained = ok_chain(first, second);

        assert_eq!(chained.next(5).unwrap_yielded(), 10);
        assert_eq!(chained.next(3).unwrap_yielded(), 4);
        assert_eq!(chained.next(10).unwrap_yielded(), 11);
    }

    #[test]
    fn test_flatten_outer_err() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(move |x: i32| {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else if x > 0 {
                Step::Complete(Ok(Ok(x)))
            } else {
                Step::Complete(Err("outer error".to_string()))
            }
        });

        let mut flattened = flatten(stage);

        assert_eq!(flattened.next(5).unwrap_yielded(), 10);
        assert_eq!(
            flattened.next(-5).unwrap_complete(),
            Err("outer error".to_string())
        );
    }

    #[test]
    fn test_flatten_inner_err() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(move |x: i32| {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else if x > 0 {
                if x < 100 {
                    Step::Complete(Ok(Ok(x)))
                } else {
                    Step::Complete(Ok(Err("inner error".to_string())))
                }
            } else {
                Step::Complete(Err("outer error".to_string()))
            }
        });

        let mut flattened = flatten(stage);

        assert_eq!(flattened.next(5).unwrap_yielded(), 10);
        assert_eq!(
            flattened.next(150).unwrap_complete(),
            Err("inner error".to_string())
        );
    }

    #[test]
    fn test_flatten_both_ok() {
        use crate::build::from_fn;
        let mut called = false;
        let stage = from_fn(move |x: i32| {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else if x > 0 {
                if x < 100 {
                    Step::Complete(Ok(Ok(x)))
                } else {
                    Step::Complete(Ok(Err("too large".to_string())))
                }
            } else {
                Step::Complete(Err("non-positive".to_string()))
            }
        });

        let mut flattened = flatten(stage);

        assert_eq!(flattened.next(5).unwrap_yielded(), 10);
        assert_eq!(flattened.next(10).unwrap_complete(), Ok(10));
    }

    // InitSans tests

    #[test]
    fn test_short_circuit_init_yields_ok() {
        let init_stage = init(
            Ok(42),
            repeat(|x: i32| if x < 0 { Err("negative") } else { Ok(x * 2) }),
        );
        let sc = short_circuit(init_stage);

        let (initial, mut stage) = sc.init().unwrap_yielded();
        assert_eq!(initial, 42);
        assert_eq!(stage.next(5).unwrap_yielded(), 10);
        assert_eq!(stage.next(3).unwrap_yielded(), 6);
    }

    #[test]
    fn test_short_circuit_init_yields_err() {
        let init_stage = init(Err("initial error"), repeat(|x: i32| Ok(x * 2)));
        let sc = short_circuit(init_stage);

        assert_eq!(sc.init().unwrap_complete(), Err("initial error"));
    }

    #[test]
    fn test_short_circuit_init_completes_immediately() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| Step::Complete::<Result<i32, &str>, i32>(100));
        let init_stage = (Ok(42), stage);
        let sc = short_circuit(init_stage);

        let (initial, mut stage) = sc.init().unwrap_yielded();
        assert_eq!(initial, 42);
        assert_eq!(stage.next(0).unwrap_complete(), Ok(100));
    }

    #[test]
    fn test_ok_map_init_first_yields() {
        use crate::build::from_fn;
        let mut called = false;
        let first_stage = from_fn(move |x: i32| -> Step<i32, Result<i32, &str>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });
        let init_first = (10, first_stage);
        let mapped = OkMap {
            state: OkMapState::OnFirst(
                init_first,
                Some(|val| init(val, repeat(move |x: i32| x + val))),
            ),
        };

        let (initial, mut stage) = mapped.init().unwrap_yielded();
        assert_eq!(initial, 10);

        // First stage continues and yields 5*2=10
        assert_eq!(stage.next(5).unwrap_yielded(), 10);

        // First completes with Ok(0), second stage starts with val=0
        assert_eq!(stage.next(0).unwrap_yielded(), 0);

        // Second stage continues: 3 + 0
        assert_eq!(stage.next(3).unwrap_yielded(), 3);
    }

    #[test]
    fn test_ok_map_init_first_completes_ok_second_yields() {
        use crate::build::from_fn;
        let first = (
            10,
            from_fn(|_: i32| Step::Complete::<i32, Result<i32, &str>>(Ok(20))),
        );
        let mapped = OkMap {
            state: OkMapState::OnFirst(
                first,
                Some(|val| init(val * 2, repeat(move |x: i32| x + val))),
            ),
        };

        let (initial, mut stage) = mapped.init().unwrap_yielded();
        assert_eq!(initial, 10);

        // First completes with Ok(20), second stage inits with (40, ...)
        assert_eq!(stage.next(0).unwrap_yielded(), 40);

        // Second stage continues: 5 + 20
        assert_eq!(stage.next(5).unwrap_yielded(), 25);
    }

    #[test]
    fn test_ok_map_init_first_completes_err() {
        use crate::build::from_fn;
        let first = (
            10,
            from_fn(|_: i32| Step::Complete::<i32, Result<i32, &str>>(Err("error"))),
        );
        let mapped = OkMap {
            state: OkMapState::OnFirst(first, Some(|val| init(val, repeat(move |x: i32| x + val)))),
        };

        let (initial, mut stage) = mapped.init().unwrap_yielded();
        assert_eq!(initial, 10);

        assert_eq!(stage.next(0).unwrap_complete(), Err("error"));
    }

    #[test]
    fn test_ok_and_then_init_first_yields() {
        use crate::build::from_fn;
        let mut called = false;
        let first_stage = from_fn(
            move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                if !called {
                    called = true;
                    Step::Yielded(Ok(x * 2))
                } else {
                    Step::Complete(Ok(x))
                }
            },
        );
        let first = (Ok(10), first_stage);
        let chained = OkAndThen {
            state: OkAndThenState::OnFirst(
                first,
                Some(|val| {
                    init(
                        Ok(val),
                        from_fn(
                            move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                                Step::Yielded(Ok(x + val))
                            },
                        ),
                    )
                }),
            ),
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, Ok(10));

        // First stage continues and yields 5*2=10
        assert_eq!(stage.next(5).unwrap_yielded(), Ok(10));

        // First completes with Ok(0), second stage starts with Ok(0)
        assert_eq!(stage.next(0).unwrap_yielded(), Ok(0));

        // Second stage continues: 3 + 0
        assert_eq!(stage.next(3).unwrap_yielded(), Ok(3));
    }

    #[test]
    fn test_ok_and_then_init_first_completes_ok_second_yields() {
        use crate::build::from_fn;
        let first = (
            Ok(10),
            from_fn(|_: i32| Step::Complete::<Result<i32, &str>, Result<i32, &str>>(Ok(20))),
        );
        let chained = OkAndThen {
            state: OkAndThenState::OnFirst(
                first,
                Some(|val| {
                    init(
                        Ok(val * 2),
                        from_fn(
                            move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                                Step::Yielded(Ok(x + val))
                            },
                        ),
                    )
                }),
            ),
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, Ok(10));

        // First completes with Ok(20), second inits with Ok(40)
        assert_eq!(stage.next(0).unwrap_yielded(), Ok(40));

        // Second stage continues: 5 + 20
        assert_eq!(stage.next(5).unwrap_yielded(), Ok(25));
    }

    #[test]
    fn test_ok_and_then_init_first_completes_err() {
        use crate::build::from_fn;
        let first = (
            Ok(10),
            from_fn(|_: i32| Step::Complete::<Result<i32, &str>, Result<i32, &str>>(Err("error"))),
        );
        let chained = OkAndThen {
            state: OkAndThenState::OnFirst(
                first,
                Some(|val| {
                    init(
                        Ok(val),
                        from_fn(
                            move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                                Step::Yielded(Ok(x + val))
                            },
                        ),
                    )
                }),
            ),
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, Ok(10));

        assert_eq!(stage.next(0).unwrap_complete(), Err("error"));
    }

    #[test]
    fn test_ok_chain_init_first_yields() {
        use crate::build::from_fn;
        let mut called = false;
        let first_stage = from_fn(move |x: i32| -> Step<i32, Result<i32, &str>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });
        let first = (10, first_stage);
        let second = repeat(|x: i32| x + 1);
        let chained = OkChain {
            stage: Some(first),
            next: second,
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, 10);

        // First stage continues and yields 5*2=10
        assert_eq!(stage.next(5).unwrap_yielded(), 10);

        // First completes with Ok(0), second stage starts with 0
        assert_eq!(stage.next(0).unwrap_yielded(), 1);
    }

    #[test]
    fn test_ok_chain_init_first_completes_ok_second_yields() {
        use crate::build::from_fn;
        let first = (
            10,
            from_fn(|_: i32| Step::Complete::<i32, Result<i32, &str>>(Ok(20))),
        );
        let second = repeat(|x: i32| x + 1);
        let chained = OkChain {
            stage: Some(first),
            next: second,
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, 10);

        // First completes with Ok(20), second starts with 20
        assert_eq!(stage.next(0).unwrap_yielded(), 21);
        assert_eq!(stage.next(50).unwrap_yielded(), 51);
    }

    #[test]
    fn test_ok_chain_init_first_completes_err() {
        use crate::build::from_fn;
        let first = (
            10,
            from_fn(|_: i32| Step::Complete::<i32, Result<i32, &str>>(Err("error"))),
        );
        let second = repeat(|x: i32| x + 1);
        let chained = OkChain {
            stage: Some(first),
            next: second,
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, 10);

        assert_eq!(stage.next(0).unwrap_complete(), Err("error"));
    }

    #[test]
    fn test_ok_chain_init_both_complete_immediately() {
        use crate::build::from_fn;
        let first = (
            10,
            from_fn(|_: i32| Step::Complete::<i32, Result<i32, &str>>(Ok(20))),
        );
        let second = from_fn(|x: i32| Step::Complete(x * 2));
        let chained = OkChain {
            stage: Some(first),
            next: second,
        };

        let (initial, mut stage) = chained.init().unwrap_yielded();
        assert_eq!(initial, 10);

        // First completes with Ok(20), second completes with 40
        assert_eq!(stage.next(0).unwrap_complete(), Ok(40));
    }

    #[test]
    fn test_flatten_init_yields_outer_err() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(
                Err::<Result<i32, &str>, &str>("outer error"),
            )
        });
        let mut flat = flatten(stage);

        assert_eq!(flat.next(0).unwrap_complete(), Err("outer error"));
    }

    #[test]
    fn test_flatten_init_yields_inner_err() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(Ok(
                Err::<i32, &str>("inner error"),
            ))
        });
        let mut flat = flatten(stage);

        assert_eq!(flat.next(0).unwrap_complete(), Err("inner error"));
    }

    #[test]
    fn test_flatten_init_completes_ok_ok() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(Ok(
                Ok::<i32, &str>(100),
            ))
        });
        let init_stage = (Ok(Ok::<i32, &str>(42)), stage);
        let flat = flatten(init_stage);

        let (initial, mut stage) = flat.init().unwrap_yielded();
        assert_eq!(initial, Ok(Ok(42)));
        assert_eq!(stage.next(0).unwrap_complete(), Ok(100));
    }

    #[test]
    fn test_flatten_init_completes_ok_err() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(Ok(
                Err::<i32, &str>("inner error"),
            ))
        });
        let init_stage = (Ok(Ok::<i32, &str>(42)), stage);
        let flat = flatten(init_stage);

        let (initial, mut stage) = flat.init().unwrap_yielded();
        assert_eq!(initial, Ok(Ok(42)));
        assert_eq!(stage.next(0).unwrap_complete(), Err("inner error"));
    }

    #[test]
    fn test_flatten_init_completes_err() {
        use crate::build::from_fn;
        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(
                Err::<Result<i32, &str>, &str>("outer error"),
            )
        });
        let init_stage = (Ok::<Result<i32, &str>, &str>(Ok::<i32, &str>(42)), stage);
        let flat = flatten(init_stage);

        let (initial, mut stage) = flat.init().unwrap_yielded();
        assert_eq!(initial, Ok(Ok(42)));
        assert_eq!(stage.next(0).unwrap_complete(), Err("outer error"));
    }

    // Extension trait tests

    #[test]
    fn test_try_sans_ok_map() {
        use crate::build::from_fn;
        use crate::result::TrySans;

        let mut called = false;
        let stage = from_fn(move |x: i32| -> Step<i32, Result<i32, &str>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });

        let mut mapped = stage.ok_map(|val| init(val, repeat(move |x: i32| x + val)));

        assert_eq!(mapped.next(5).unwrap_yielded(), 10);
        assert_eq!(mapped.next(3).unwrap_yielded(), 3);
        assert_eq!(mapped.next(7).unwrap_yielded(), 10);
    }

    #[test]
    fn test_try_sans_ok_and_then() {
        use crate::build::from_fn;
        use crate::result::TrySans;

        let mut called = false;
        let stage = from_fn(
            move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                if !called {
                    called = true;
                    Step::Yielded(Ok(x * 2))
                } else {
                    Step::Complete(Ok(x))
                }
            },
        );

        let mut chained = stage.ok_and_then(|val| {
            let mut inner_called = false;
            init(
                Ok(val),
                from_fn(
                    move |x: i32| -> Step<Result<i32, &str>, Result<i32, &str>> {
                        if !inner_called {
                            inner_called = true;
                            Step::Yielded(Ok(x + val))
                        } else {
                            Step::Complete(Ok(x))
                        }
                    },
                ),
            )
        });

        assert_eq!(chained.next(5).unwrap_yielded(), Ok(10));
        assert_eq!(chained.next(3).unwrap_yielded(), Ok(3));
        assert_eq!(chained.next(7).unwrap_yielded(), Ok(10));
    }

    #[test]
    fn test_try_sans_ok_chain() {
        use crate::build::from_fn;
        use crate::result::TrySans;

        let mut called = false;
        let first = from_fn(move |x: i32| -> Step<i32, Result<i32, &str>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });
        let second = repeat(|x: i32| x + 1);

        let mut chained = first.ok_chain(second);

        assert_eq!(chained.next(5).unwrap_yielded(), 10);
        assert_eq!(chained.next(3).unwrap_yielded(), 4);
        assert_eq!(chained.next(10).unwrap_yielded(), 11);
    }

    #[test]
    fn test_try_sans_flatten() {
        use crate::build::from_fn;
        use crate::result::TrySans;

        let mut called = false;
        #[allow(clippy::type_complexity)]
        let stage = from_fn(move |x: i32| -> Step<
            Result<Result<i32, &str>, &str>,
            Result<Result<i32, &str>, &str>,
        > {
            if !called {
                called = true;
                Step::Yielded(Ok(Ok(x * 2)))
            } else {
                Step::Complete(Ok(Ok(x)))
            }
        });

        let mut flattened = stage.flatten();

        assert_eq!(flattened.next(5).unwrap_yielded(), Ok(Ok(10)));
        assert_eq!(flattened.next(10).unwrap_complete(), Ok(10));
    }

    #[test]
    fn test_try_init_sans_ok_map() {
        use crate::build::from_fn;
        use crate::result::TryInitSans;

        let mut called = false;
        let first_stage = from_fn(move |x: i32| -> Step<i32, Result<i32, &str>> {
            if !called {
                called = true;
                Step::Yielded(x * 2)
            } else {
                Step::Complete(Ok(x))
            }
        });
        let init_first = (10, first_stage);
        let mapped = init_first.ok_map(|val| init(val, repeat(move |x: i32| x + val)));

        let (initial, mut stage) = mapped.init().unwrap_yielded();
        assert_eq!(initial, 10);

        assert_eq!(stage.next(5).unwrap_yielded(), 10);
        assert_eq!(stage.next(0).unwrap_yielded(), 0);
        assert_eq!(stage.next(3).unwrap_yielded(), 3);
    }

    #[test]
    fn test_try_init_sans_flatten() {
        use crate::build::from_fn;
        use crate::result::TryInitSans;

        let stage = from_fn(|_: i32| {
            Step::Complete::<Result<Result<i32, &str>, &str>, Result<Result<i32, &str>, &str>>(Ok(
                Ok::<i32, &str>(100),
            ))
        });
        let init_stage = (Ok(Ok::<i32, &str>(42)), stage);
        let flat = init_stage.flatten();

        let (initial, mut stage) = flat.init().unwrap_yielded();
        assert_eq!(initial, Ok(Ok(42)));
        assert_eq!(stage.next(0).unwrap_complete(), Ok(100));
    }
}
