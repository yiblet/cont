#![forbid(unsafe_code)]
//! # Cont: Composable Continuation-Based Programming
//!
//! Build composable computations that can yield intermediate values and be driven
//! to completion by external input.
//!
//! ## Core Traits
//!
//! - **[`Sans<I, O>`]**: Stateful computations that process input and yield values
//! - **[`InitSans<I, O>`]**: Computations that provide initial output before processing input
//!
//! ## Key Features
//!
//! - **Composable**: Chain stages together with `.chain()`
//! - **Transformable**: Use `.map_input()`, `.map_yield()`, `.map_done()`
//! - **Async Support**: Both sync and async execution with `handle()` and `handle_async()`
//!
//! ## Example
//!
//! ```
//! use cont::prelude::*;
//!
//! // Build a pipeline that yields initial value, processes input, then finishes
//! let pipeline = init_once(10, |x: i32| x * 2)  // Yields 10, then multiplies input by 2
//!     .chain(once(|x: i32| x + 1));              // Adds 1 to input, then completes
//!
//! // Drive the pipeline with responses to each yield
//! let result = handle(pipeline, |output| output + 5);
//! ```
//!
//! ## Module Organization
//!
//! This library is organized by capability:
//!
//! - **[`build`]** - Creating new continuation stages
//! - **[`compose`]** - Chaining and transforming continuations
//! - **[`poll`]** - Universal adapter implementing both [`Sans`] and [`InitSans`] for bridging APIs
//! - **[`concurrent`]** - Running multiple continuations concurrently
//! - **[`sequential`]** - Running continuations one after another
//! - **[`run`]** - Executing continuation pipelines
//! - **[`prelude`]** - Common imports for quick start
//!
//! ## Common Functions
//!
//! **Building Stages:**
//! - [`once(f)`](build::once) - Apply function once, then complete
//! - [`repeat(f)`](build::repeat) - Apply function repeatedly
//! - [`init_once(value, f)`](build::init_once) - Yield initial value, then apply function once
//! - [`chain(a, b)`](compose::chain) - Run stage `a` to completion, then run stage `b`
//!
//! **Execution:**
//! - [`handle(stage, responder)`](run::handle) - Drive computation with sync responses
//! - [`handle_async(stage, responder)`](run::handle_async) - Drive computation with async responses

// Core modules (essential types)
mod step;
mod sans;
mod init;

// Capability modules
pub mod build;
pub mod compose;
pub mod poll;
pub mod concurrent;
pub mod sequential;
pub mod run;

// Convenience
pub mod prelude;

// Re-export essential types at root
pub use step::Step;
pub use sans::{Sans, PoisonError};
pub use init::InitSans;
