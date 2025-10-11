//! Combining coroutines together
//!
//! This module provides functions for chaining and transforming coroutines.

mod chain;
mod map;

// Re-export composition operations
pub use chain::{AndThen, Chain, and_then, chain, init_chain};
pub use map::{
    MapInput, MapReturn, MapYield, init_map_input, init_map_return, init_map_yield, map_input,
    map_return, map_yield,
};
