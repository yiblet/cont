//! Combining continuations together
//!
//! This module provides functions for chaining and transforming continuations.

mod chain;
mod map;

// Re-export composition operations
pub use chain::{chain, init_chain, Chain, and_then, AndThen};
pub use map::{map_input, map_yield, map_return, MapInput, MapYield, MapReturn};
