//! # Cont: Composable Continuation-Based Programming
//!
//! Build composable computations that can yield intermediate values and be driven
//! to completion by external input.
//!
//! ## Core Traits
//!
//! - **[`Sans<A>`]**: Stateful computations that process input and yield values
//! - **[`InitSans<A>`]**: Computations that provide initial output before processing input
//!
//! ## Key Features
//!
//! - **Composable**: Chain stages together with `.chain()`
//! - **Transformable**: Use `.map_input()`, `.map_yielded()`, `.map_complete()`
//! - **Async Support**: Both sync and async execution with `handle()` and `handle_async()`
//!
//! ## Example
//!
//! ```
//! use cont::*;
//!
//! // Build a pipeline that yields initial value, processes input, then finishes
//! let pipeline = init_once(10, |x: i32| x * 2)  // Yields 10, then multiplies input by 2
//!     .chain(once(|x: i32| x + 1));              // Adds 1 to input, then completes
//!
//! // Drive the pipeline with responses to each yield
//! let result = handle(pipeline, |yielded| yielded + 5);
//! ```
//!
//! ## Common Functions
//!
//! **Building Stages:**
//! - [`once(f)`] - Apply function once, then complete
//! - [`repeat(f)`] - Apply function repeatedly
//! - [`init_once(value, f)`] - Yield initial value, then apply function once
//! - [`chain(a, b)`] - Run stage `a` to completion, then run stage `b`
//!
//! **Execution:**
//! - [`handle(stage, responder)`] - Drive computation with sync responses
//! - [`handle_async(stage, responder)`] - Drive computation with async responses

mod handler;
mod init;
mod sans;
mod step;

pub use handler::*;
pub use init::*;
pub use sans::*;
pub use step::*;
