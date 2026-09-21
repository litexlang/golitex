//! Store accepted facts into the env and run local inference from them.
//! Callers verify first; this path is not open-ended proof search.

pub mod store_fact;
pub mod store_fact_and_infer_result;

pub use store_fact_and_infer_result::{
    ChainTransitiveCite, StoreAndComponentResult, StoreAndFactResult, StoreAtomicFactResult,
    StoreChainAdjacentResult, StoreChainFactResult, StoreChainTransitiveClosureResult,
    StoreExistFactResult, StoreFactAndInferResult, StoreNotForallFactResult, StoreOrFactResult,
};
