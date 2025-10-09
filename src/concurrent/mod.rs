//! Run multiple continuations concurrently
//!
//! This module provides polling and joining operations for concurrent execution.

mod poll;
mod join;

// Re-export concurrent operations
pub use poll::{poll, init_poll, Poll, PollOutput, Pollable, PollError};
pub use join::{join, join_vec, init_join, init_join_vec, Join, JoinVec, JoinEnvelope, JoinError};
