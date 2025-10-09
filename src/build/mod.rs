//! Building coroutines from scratch
//!
//! This module provides functions and types for creating new coroutine stages.

mod func;
mod init;

// Re-export building blocks
pub use func::{once, repeat, from_fn, Once, Repeat, FromFn};
pub use init::{init, init_once, init_repeat, init_from_fn};
