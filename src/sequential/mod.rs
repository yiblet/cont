//! Run coroutines one after another
//!
//! This module provides sequential execution combinators.

mod many;

// Re-export sequential operations
pub use many::{Many, many};
