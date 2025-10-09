//! Run multiple continuations concurrently
//!
//! This module provides joining operations for concurrent execution.

mod join;

// Re-export concurrent operations
pub use join::{join, join_vec, init_join, init_join_vec, Join, JoinVec, JoinEnvelope, JoinError};
