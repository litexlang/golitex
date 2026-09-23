use crate::new_pipeline::ast::fact::{
    AndFact, AtomicFact, ChainFact, ExistShapedFact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::runtime::FactId;

// store_fact: index by shape into known-* / ExecEnv fields (not new mathematics).
pub enum StoreFactResult {
    AtomicFact(StoreAtomicFactResult),
    AndFact(StoreAndFactResult),
    ChainFact(StoreChainFactStorePart),
    OrFact(StoreOrFactResult),
    ExistShapedFact(StoreExistShapedFactResult),
    NotForallFact(StoreNotForallFactStorePart),
    ForallFact(StoreForallFactResult),
    ForallFactWithIff(StoreForallFactWithIffResult),
}

// infer_fact: only generate extra facts and store them (via store_inferred / store_fact_and_infer).
// Never used to poke unrelated ExecEnv indexes — that belongs to store_fact.
pub enum InferFactResult {
    AtomicFact(InferAtomicFactResult),
    AndFact(InferAndFactResult),
    ChainFact(InferChainFactResult),
    OrFact(InferOrFactResult),
    ExistShapedFact(InferExistShapedFactResult),
    NotForallFact(InferNotForallFactResult),
    ForallFact(InferForallFactResult),
    ForallFactWithIff(InferForallFactWithIffResult),
}

// Option A: always store then infer as two explicit stages.
pub struct StoreFactAndInferResult {
    pub store: StoreFactResult,
    pub infer: InferFactResult,
}

pub struct StoreAtomicFactResult {
    pub fact_id: FactId,
    pub fact: AtomicFact,
}

pub struct StoreAndFactResult {
    pub whole_fact_id: FactId,
    pub fact: AndFact,
    pub components: Vec<StoreAndComponentResult>,
}

pub struct StoreAndComponentResult {
    pub component_index: usize,
    pub fact_id: FactId,
    pub fact: AtomicFact,
}

pub struct StoreChainFactStorePart {
    pub whole_fact_id: FactId,
    pub fact: ChainFact,
    pub adjacent: Vec<StoreChainAdjacentResult>,
}

pub struct StoreChainAdjacentResult {
    pub edge_index: usize,
    pub fact_id: FactId,
    pub fact: AtomicFact,
}

pub struct StoreOrFactResult {
    pub whole_fact_id: FactId,
    pub fact: OrFact,
}

pub struct StoreExistShapedFactResult {
    pub whole_fact_id: FactId,
    pub fact: ExistShapedFact,
}

pub struct StoreNotForallFactStorePart {
    pub whole_fact_id: FactId,
    pub fact: NotForallFact,
}

pub struct StoreForallFactResult {
    pub fact_id: FactId,
    pub fact: ForallFact,
}

pub struct StoreForallFactWithIffResult {
    pub fact_id: FactId,
    pub fact: ForallFactWithIff,
    pub forward: StoreForallFactResult,
    pub reverse: StoreForallFactResult,
}

pub enum InferAtomicFactResult {
    // One equal fact may fire many equality-infer rules.
    EqualFact(Vec<InferEqualityResult>),
    // One non-equal atomic may fire many shape-specific rules.
    ExceptEquality(Vec<InferAtomicExceptEqualityResult>),
}

// One equality-infer rule application (evidence + derived facts).
pub enum InferEqualityResult {
    // Rule: equality to literal cart/tuple records shape facts on the other side.
    CartTupleShape(InferEqualFactCartTupleShapeResult),
    // Rule: `0 = u - v` or `u - v = 0` ⇒ `u = v`.
    SubtractionEqualsZero(InferEqualFactSubtractionEqualsZeroResult),
}

pub struct InferEqualFactCartTupleShapeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferEqualFactSubtractionEqualsZeroResult {
    pub derived: Box<StoreFactAndInferResult>,
}

// One non-equal atomic infer rule application.
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

pub struct InferAndFactResult {
    pub components: Vec<InferAtomicFactResult>,
}

pub struct InferChainFactResult {
    pub adjacent_infers: Vec<InferAtomicFactResult>,
    pub transitive_closures: Vec<InferChainTransitiveClosureResult>,
}

pub struct InferChainTransitiveClosureResult {
    pub cite: ChainTransitiveCite,
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premise_edge_indexes: Vec<usize>,
    pub derived: Box<StoreFactAndInferResult>,
}

pub enum ChainTransitiveCite {
    BuiltinEquality,
    BuiltinNumericOrder,
    KnownTransitive { prop_name: AtomicName },
}

pub enum InferOrFactResult {
    // Or is not split on store; do not eager-infer a branch.
    NoInfer,
}

// Mirrors ExistShapedFact: plain exist has no default infer; exist! / not exist do.
pub enum InferExistShapedFactResult {
    Exist(InferPlainExistFactResult),
    ExistUnique(InferExistUniqueFactResult),
    NotExist(InferNotExistFactResult),
}

pub enum InferPlainExistFactResult {
    NoInfer,
}

pub enum InferExistUniqueFactResult {
    // Rule: `exist!` exposes componentwise uniqueness forall (Manual Builtin Inference).
    UniquenessForall(InferExistUniqueUniquenessForallResult),
    NoInfer,
}

pub struct InferExistUniqueUniquenessForallResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub enum InferNotExistFactResult {
    // Rule: `not exist` exposes De Morgan forall when body shape is supported.
    DemorganForall(InferNotExistDemorganForallResult),
    NoInfer,
}

pub struct InferNotExistDemorganForallResult {
    pub derived: Box<StoreFactAndInferResult>,
}

pub struct InferNotForallFactResult {
    pub derived_exist: Box<StoreFactAndInferResult>,
}

pub enum InferForallFactResult {
    // Forall is recorded for later use/instantiation; no eager conclusions here.
    NoInfer,
}

pub enum InferForallFactWithIffResult {
    // Bidirectional split belongs to store_fact, not infer.
    NoInfer,
}

impl StoreFactResult {
    pub fn primary_fact_id(&self) -> FactId {
        match self {
            Self::AtomicFact(r) => r.fact_id,
            Self::AndFact(r) => r.whole_fact_id,
            Self::ChainFact(r) => r.whole_fact_id,
            Self::OrFact(r) => r.whole_fact_id,
            Self::ExistShapedFact(r) => r.whole_fact_id,
            Self::NotForallFact(r) => r.whole_fact_id,
            Self::ForallFact(r) => r.fact_id,
            Self::ForallFactWithIff(r) => r.fact_id,
        }
    }

    pub fn atomic_components(&self) -> Vec<(FactId, AtomicFact)> {
        match self {
            Self::AtomicFact(r) => vec![(r.fact_id, r.fact.clone())],
            Self::AndFact(r) => r
                .components
                .iter()
                .map(|c| (c.fact_id, c.fact.clone()))
                .collect(),
            Self::ChainFact(r) => r
                .adjacent
                .iter()
                .map(|a| (a.fact_id, a.fact.clone()))
                .collect(),
            Self::OrFact(_)
            | Self::ExistShapedFact(_)
            | Self::NotForallFact(_)
            | Self::ForallFact(_)
            | Self::ForallFactWithIff(_) => Vec::new(),
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::AtomicFact(r) => vec![r.fact_id],
            Self::AndFact(r) => {
                let mut ids = Vec::with_capacity(1 + r.components.len());
                ids.push(r.whole_fact_id);
                for c in &r.components {
                    ids.push(c.fact_id);
                }
                ids
            }
            Self::ChainFact(r) => {
                let mut ids = Vec::with_capacity(1 + r.adjacent.len());
                ids.push(r.whole_fact_id);
                for a in &r.adjacent {
                    ids.push(a.fact_id);
                }
                ids
            }
            Self::OrFact(r) => vec![r.whole_fact_id],
            Self::ExistShapedFact(r) => vec![r.whole_fact_id],
            Self::NotForallFact(r) => vec![r.whole_fact_id],
            Self::ForallFact(r) => vec![r.fact_id],
            Self::ForallFactWithIff(r) => vec![r.forward.fact_id, r.reverse.fact_id],
        }
    }
}

impl InferFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::AtomicFact(r) => r.stored_fact_ids(),
            Self::AndFact(r) => {
                let mut ids = Vec::new();
                for c in &r.components {
                    ids.extend(c.stored_fact_ids());
                }
                ids
            }
            Self::ChainFact(r) => {
                let mut ids = Vec::new();
                for a in &r.adjacent_infers {
                    ids.extend(a.stored_fact_ids());
                }
                for c in &r.transitive_closures {
                    ids.extend(c.derived.stored_fact_ids());
                }
                ids
            }
            Self::OrFact(_) | Self::ForallFact(_) | Self::ForallFactWithIff(_) => Vec::new(),
            Self::ExistShapedFact(r) => r.stored_fact_ids(),
            Self::NotForallFact(r) => r.derived_exist.stored_fact_ids(),
        }
    }
}

impl InferExistShapedFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::Exist(_) => Vec::new(),
            Self::ExistUnique(r) => match r {
                InferExistUniqueFactResult::UniquenessForall(u) => u.derived.stored_fact_ids(),
                InferExistUniqueFactResult::NoInfer => Vec::new(),
            },
            Self::NotExist(r) => match r {
                InferNotExistFactResult::DemorganForall(d) => d.derived.stored_fact_ids(),
                InferNotExistFactResult::NoInfer => Vec::new(),
            },
        }
    }
}

impl InferAtomicFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::EqualFact(rules) => {
                let mut ids = Vec::new();
                for rule in rules {
                    ids.extend(rule.stored_fact_ids());
                }
                ids
            }
            Self::ExceptEquality(rules) => {
                let mut ids = Vec::new();
                for rule in rules {
                    ids.extend(rule.stored_fact_ids());
                }
                ids
            }
        }
    }
}

impl InferEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::CartTupleShape(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::SubtractionEqualsZero(r) => r.derived.stored_fact_ids(),
        }
    }
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

impl StoreFactAndInferResult {
    pub fn primary_fact_id(&self) -> FactId {
        self.store.primary_fact_id()
    }

    pub fn atomic_components(&self) -> Vec<(FactId, AtomicFact)> {
        self.store.atomic_components()
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        let mut ids = self.store.stored_fact_ids();
        ids.extend(self.infer.stored_fact_ids());
        ids
    }
}
