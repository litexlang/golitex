use crate::new_pipeline::runtime::FactId;

use super::StoreFactAndInferResult;

// One non-equal atomic infer rule hit (parallel to AtomicExceptEquality search
// proof arms). Verify keeps a single winning proof; infer pushes every hit into
// the parent Vec and stores each rule's derived facts.
pub enum InferAtomicExceptEqualityResult {
    // `$P(args)` → parameter-type obligations.
    NormalAtomicParamTypes(InferNormalAtomicParamTypesProjectedResult),
    // `$P(args)` → instantiated iff facts (one layer).
    NormalAtomicExpandDefinition(InferExpandDefinitionResult),
    // `x $in {y S: …}` → base membership + filters.
    InFactSetBuilder(InferSetBuilderMembershipProjectionResult),
    // `A $in power_set(B)` → `A $subset B`.
    InFactPowerSet(InferPowerSetMembershipProjectionResult),
    // `x $in N` → `x >= 0`.
    InFactNaturalNonnegative(InferInFactNaturalNonnegativeResult),
    // `x $in Q+/R+/N+` → `0 < x`.
    InFactPositiveStandardSet(InferInFactPositiveStandardSetResult),
    // `x $in Q-/Z-/R-` → `x < 0`.
    InFactNegativeStandardSet(InferInFactNegativeStandardSetResult),
    // `x $in Q*/Z*/R*/C*` → `x != 0`.
    InFactNonzeroStandardSet(InferInFactNonzeroStandardSetResult),
    // `x $in {a}` → `x = a`.
    InFactListSetSingletonEqual(InferInFactListSetSingletonEqualResult),
    // `x $in {a, b, …}` → `x = a or x = b or …`.
    InFactListSetOrEqualities(InferInFactListSetOrEqualitiesResult),
    // `x $in union(A, B)` → `x $in A or x $in B`.
    InFactUnionOr(InferInFactUnionOrResult),
    // `x $in intersect(A, B)` → `x $in A` and `x $in B`.
    InFactIntersectBoth(InferInFactIntersectBothResult),
    // `x $in set_minus(A, B)` → `x $in A`, `not x $in B` (+ optional `x != a`).
    InFactSetMinusSplit(InferInFactSetMinusSplitResult),
    // `x $in cart(A, B, …)` → tuple shape + coordinate memberships.
    InFactCartProjection(InferInFactCartProjectionResult),
    // `x $in range(a, b)` → `x $in Z`, bounds (+ optional singleton eq).
    InFactRange(InferInFactRangeResult),
    // `x $in closed_range(a, b)` → `x $in Z`, bounds (+ optional singleton eq).
    InFactClosedRange(InferInFactClosedRangeResult),
    // `x $in '(a, b]` etc. → `x $in R` + endpoint bounds.
    InFactRealInterval(InferInFactRealIntervalResult),
    // `x $in '[a,)` etc. → `x $in R` + one bound.
    InFactOneSideRealInterval(InferInFactOneSideRealIntervalResult),
    // `x $in S` with `S = fn(...)` → `x $in fn(...)`.
    InFactEqualFnSetExpand(InferInFactEqualFnSetExpandResult),
    // `z $in fn_range(f)` → `z $in ret` (+ optional preimage exist).
    InFactFnRange(InferInFactFnRangeResult),
    // `x $in finite_seq(S, n)` → `x $in fn(i N+: i <= n) S`.
    InFactFiniteSeqExpand(InferInFactFiniteSeqExpandResult),
    // `x $in seq(S)` → `x $in fn(i N+) S`.
    InFactSeqExpand(InferInFactSeqExpandResult),
    // `x $in family_union(F)` → `exist item F st {x $in item}`.
    InFactFamilyUnion(InferInFactFamilyUnionResult),
    // `x $in index_union(I, X, A)` → ambient + exist fiber.
    InFactIndexUnion(InferInFactIndexUnionResult),
    // `x $in index_intersect(I, X, A)` → ambient + forall fiber.
    InFactIndexIntersect(InferInFactIndexIntersectResult),
    // `f $in index_cart(I, S, g)` → FnSet membership + `$is_choice_function_for`.
    InFactIndexCart(InferInFactIndexCartResult),
    // Order vs resolved numeric bound → sign vs 0.
    LessSign(InferNumericOrderSignResult),
    GreaterSign(InferNumericOrderSignResult),
    LessEqualSign(InferNumericOrderSignResult),
    GreaterEqualSign(InferNumericOrderSignResult),
    // Order vs 0 → flip by multiplying left by (-1).
    OrderFlipMulMinusOne(InferOrderFlipMulMinusOneResult),
    // `$is_cart(C)` → `cart_dim(C) >= 2`.
    IsCartDimensionLowerBound(InferIsCartDimensionLowerBoundResult),
    // `A $subset B` → `forall x A: x $in B`.
    SubsetElementwiseMembership(InferSubsetElementwiseMembershipResult),
    // `A $superset B` → `forall x B: x $in A`.
    SupersetElementwiseMembership(InferSupersetElementwiseMembershipResult),
}

pub struct InferNormalAtomicParamTypesProjectedResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferExpandDefinitionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferSetBuilderMembershipProjectionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferPowerSetMembershipProjectionResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactNaturalNonnegativeResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactPositiveStandardSetResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactNegativeStandardSetResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactNonzeroStandardSetResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactListSetSingletonEqualResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactListSetOrEqualitiesResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactUnionOrResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactIntersectBothResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactSetMinusSplitResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactCartProjectionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactRangeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactClosedRangeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactRealIntervalResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactOneSideRealIntervalResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactEqualFnSetExpandResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactFnRangeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactFiniteSeqExpandResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactSeqExpandResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactFamilyUnionResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferInFactIndexUnionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactIndexIntersectResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferInFactIndexCartResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferNumericOrderSignResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferOrderFlipMulMinusOneResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferIsCartDimensionLowerBoundResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferSubsetElementwiseMembershipResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferSupersetElementwiseMembershipResult {
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferAtomicExceptEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::NormalAtomicParamTypes(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::NormalAtomicExpandDefinition(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactSetBuilder(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactPowerSet(r) => r.derived.stored_fact_ids(),
            Self::InFactNaturalNonnegative(r) => r.derived.stored_fact_ids(),
            Self::InFactPositiveStandardSet(r) => r.derived.stored_fact_ids(),
            Self::InFactNegativeStandardSet(r) => r.derived.stored_fact_ids(),
            Self::InFactNonzeroStandardSet(r) => r.derived.stored_fact_ids(),
            Self::InFactListSetSingletonEqual(r) => r.derived.stored_fact_ids(),
            Self::InFactListSetOrEqualities(r) => r.derived.stored_fact_ids(),
            Self::InFactUnionOr(r) => r.derived.stored_fact_ids(),
            Self::InFactIntersectBoth(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactSetMinusSplit(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactCartProjection(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactRange(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactClosedRange(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactRealInterval(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactOneSideRealInterval(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactEqualFnSetExpand(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactFnRange(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactFiniteSeqExpand(r) => r.derived.stored_fact_ids(),
            Self::InFactSeqExpand(r) => r.derived.stored_fact_ids(),
            Self::InFactFamilyUnion(r) => r.derived.stored_fact_ids(),
            Self::InFactIndexUnion(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactIndexIntersect(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::InFactIndexCart(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::LessSign(r)
            | Self::GreaterSign(r)
            | Self::LessEqualSign(r)
            | Self::GreaterEqualSign(r) => r.derived.stored_fact_ids(),
            Self::OrderFlipMulMinusOne(r) => r.derived.stored_fact_ids(),
            Self::IsCartDimensionLowerBound(r) => r.derived.stored_fact_ids(),
            Self::SubsetElementwiseMembership(r) => r.derived.stored_fact_ids(),
            Self::SupersetElementwiseMembership(r) => r.derived.stored_fact_ids(),
        }
    }
}
