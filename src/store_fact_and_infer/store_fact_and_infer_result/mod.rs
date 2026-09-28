//! Store / infer result types for `store_fact_and_infer`.
//!
//! Granularity mirrors verify fact results: one file per top-level shape family
//! (store dispatcher, equality rules, except-equality rules, non-atomic infer),
//! not one file per rule payload.

mod store_fact_result;
mod store_and_infer_result;
mod infer_equality_result;
mod infer_atomic_except_equality_result;
mod infer_atomic_fact_result;
mod infer_fact_result;

pub use store_fact_result::*;
pub use store_and_infer_result::*;
pub use infer_equality_result::*;
pub use infer_atomic_except_equality_result::*;
pub use infer_atomic_fact_result::*;
pub use infer_fact_result::*;
