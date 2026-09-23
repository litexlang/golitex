//! Store accepted facts into the env and run local inference from them.
//!
//! Layering:
//! - `store_fact`: index by fact shape into known-* / ExecEnv fields
//! - `infer_fact`: only generate extra facts and store them (never raw Env field pokes)
//! - `store_fact_and_infer`: `{ store, infer }` (seed already verified by caller)
//! - `store_inferred_fact_and_infer`: WD check, then store_fact_and_infer (for infer children)
//!
//! Non-atomic infer is not uniformly "atomic packaging":
//! - And / Chain-adjacent: delegate to atomic infer (+ Chain transitive closure)
//! - NotForall / ExistUnique / NotExist: shape rewrite → store_inferred
//! - Or / plain Exist / Forall*: intentionally NoInfer
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
    InferEqualFactCartTupleShapeResult, InferEqualFactSubtractionEqualsZeroResult,
    InferEqualityResult, InferExistShapedFactResult, InferExistUniqueFactResult,
    InferExistUniqueUniquenessForallResult, InferExpandDefinitionResult, InferFactResult,
    InferForallFactResult, InferForallFactWithIffResult, InferInFactCartProjectionResult,
    InferInFactClosedRangeResult, InferInFactIntersectBothResult,
    InferInFactListSetOrEqualitiesResult, InferInFactListSetSingletonEqualResult,
    InferInFactNaturalNonnegativeResult, InferInFactNegativeStandardSetResult,
    InferInFactNonzeroStandardSetResult, InferInFactOneSideRealIntervalResult,
    InferInFactPositiveStandardSetResult, InferInFactRangeResult, InferInFactRealIntervalResult,
    InferInFactSetMinusSplitResult, InferInFactUnionOrResult, InferIsCartDimensionLowerBoundResult,
    InferNormalAtomicParamTypesProjectedResult, InferNotExistDemorganForallResult,
    InferNotExistFactResult, InferNotForallFactResult, InferNumericOrderSignResult,
    InferOrderFlipMulMinusOneResult, InferOrFactResult, InferPlainExistFactResult,
    InferPowerSetMembershipProjectionResult, InferSetBuilderMembershipProjectionResult,
    InferSubsetElementwiseMembershipResult, InferSupersetElementwiseMembershipResult,
    StoreAndComponentResult, StoreAndFactResult, StoreAtomicFactResult, StoreChainAdjacentResult,
    StoreChainFactStorePart, StoreExistShapedFactResult, StoreFactAndInferResult, StoreFactResult,
    StoreForallFactResult, StoreForallFactWithIffResult, StoreNotForallFactStorePart,
    StoreOrFactResult,
};
