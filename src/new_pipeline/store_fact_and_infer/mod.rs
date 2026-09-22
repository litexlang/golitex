//! Store accepted facts into the env and run local inference from them.
//!
//! Layering:
//! - `store_fact`: index by fact shape into known-* / ExecEnv fields
//! - `infer_fact`: only generate extra facts and store them (never raw Env field pokes)
//! - `store_fact_and_infer`: `{ store, infer }` (seed already verified by caller)
//! - `store_inferred_fact_and_infer`: WD check, then store_fact_and_infer (for infer children)
//!
//! Callers verify the seed fact first; this path is not open-ended proof search.

pub mod helper;
pub mod infer_fact;
pub mod store_fact;
pub mod store_fact_and_infer;
pub mod store_fact_and_infer_result;

pub use store_fact_and_infer_result::{
    ChainTransitiveCite, InferAndFactResult, InferAtomicExceptEqualityResult,
    InferAtomicFactResult, InferChainFactResult, InferChainTransitiveClosureResult,
    InferEqualFactCartTupleShapeResult, InferEqualFactResult, InferExistShapedFactResult,
    InferExpandDefinitionResult, InferFactResult, InferFnEqualInFactResult,
    InferForallFactResult, InferForallFactWithIffResult, InferGreaterEqualFactResult,
    InferGreaterFactResult, InferInFactResult, InferIsCartFactResult, InferIsFiniteSetFactResult,
    InferIsNonemptySetFactResult, InferIsSetFactResult, InferIsTupleFactResult,
    InferLessEqualFactResult, InferLessFactResult, InferNormalAtomicFactResult,
    InferNotEqualFactResult, InferNotFnEqualInFactResult, InferNotForallFactResult,
    InferNotGreaterEqualFactResult, InferNotGreaterFactResult, InferNotInFactResult,
    InferNotIsCartFactResult, InferNotIsFiniteSetFactResult, InferNotIsNonemptySetFactResult,
    InferNotIsSetFactResult, InferNotIsTupleFactResult, InferNotLessEqualFactResult,
    InferNotLessFactResult, InferNotNormalAtomicFactResult, InferNotSubsetFactResult,
    InferNotSupersetFactResult, InferOrFactResult, InferPowerSetMembershipProjectionResult,
    InferSetBuilderMembershipProjectionResult, InferSubsetFactResult, InferSupersetFactResult,
    StoreAndComponentResult, StoreAndFactResult, StoreAtomicFactResult, StoreChainAdjacentResult,
    StoreChainFactStorePart, StoreExistShapedFactResult, StoreFactAndInferResult, StoreFactResult,
    StoreForallFactResult, StoreForallFactWithIffResult, StoreNotForallFactStorePart,
    StoreOrFactResult,
};
