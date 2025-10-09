//! Combining coroutines together
//!
//! This module provides functions for chaining and transforming coroutines.

mod chain;
mod map;

// Re-export composition operations
pub use chain::{chain, init_chain, Chain, and_then, AndThen};
pub use map::{
    map_input, init_map_input,
    map_yield, init_map_yield,
    map_return, init_map_return,
    MapInput, MapYield, MapReturn
};
