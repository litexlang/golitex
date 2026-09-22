//! Store accepted facts into the env and run local inference from them.
//!
//! Layering:
//! - `store_fact`: index by fact shape into known-* / special properties
//! - `infer_fact`: derive routine consequences and store them
//! - `store_fact_and_infer`: store_fact then infer_fact
//!
//! Callers verify first; this path is not open-ended proof search.

pub mod helper;
pub mod infer_fact;
pub mod store_fact;
pub mod store_fact_and_infer;
pub mod store_fact_and_infer_result;

pub use store_fact_and_infer_result::{
    ChainTransitiveCite, InferFactResult, StoreAndComponentResult, StoreAndFactResult,
    StoreAtomicFactResult, StoreChainAdjacentResult, StoreChainFactResult,
    StoreChainFactStorePart, StoreChainTransitiveClosureResult, StoreExistFactResult,
    StoreFactAndInferResult, StoreFactResult, StoreForallFactResult, StoreForallFactWithIffResult,
    StoreNotForallFactResult, StoreNotForallFactStorePart, StoreOrFactResult,
};
