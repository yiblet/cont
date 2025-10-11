//! Building coroutines from scratch
//!
//! This module provides functions and types for creating new coroutine stages.

mod func;
mod init;

// Re-export building blocks
pub use func::{FromFn, Once, Repeat, from_fn, once, repeat};
pub use init::{init, init_from_fn, init_once, init_repeat};
