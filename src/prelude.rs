//! Commonly used imports
//!
//! Use `use sans::prelude::*;` for quick access to the most common types and functions.

// Core types
pub use crate::{Step, Sans, InitSans};

// Most common constructors
pub use crate::build::{
    once, repeat, from_fn,
    init, init_once, init_repeat, init_from_fn,
};

// Composition
pub use crate::compose::chain;

// Transformations
pub use crate::compose::{map_input, map_yield, map_return};

// Polling (universal adapter)
pub use crate::poll::{poll, init_poll};

// Execution
pub use crate::run::{handle, handle_async};
