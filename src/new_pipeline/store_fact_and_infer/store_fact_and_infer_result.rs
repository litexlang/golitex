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
    EqualFact(InferEqualFactResult),
    ExceptEquality(InferAtomicExceptEqualityResult),
}

pub struct InferEqualFactResult {
    // Empty when neither side is a literal cart/tuple usable for shape facts.
    pub cart_tuple_shape: Option<InferEqualFactCartTupleShapeResult>,
}

// Rule: equality to literal cart/tuple records shape facts on the other side.
pub struct InferEqualFactCartTupleShapeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

// Mirrors atomic-except-equality `AtomicFact` constructors; each arm owns that
// shape's infer evidence (no shared Option/Option stage bag).
pub enum InferAtomicExceptEqualityResult {
    NormalAtomicFact(InferNormalAtomicFactResult),
    LessFact(InferLessFactResult),
    GreaterFact(InferGreaterFactResult),
    LessEqualFact(InferLessEqualFactResult),
    GreaterEqualFact(InferGreaterEqualFactResult),
    IsSetFact(InferIsSetFactResult),
    IsNonemptySetFact(InferIsNonemptySetFactResult),
    IsFiniteSetFact(InferIsFiniteSetFactResult),
    InFact(InferInFactResult),
    IsCartFact(InferIsCartFactResult),
    IsTupleFact(InferIsTupleFactResult),
    SubsetFact(InferSubsetFactResult),
    SupersetFact(InferSupersetFactResult),
    NotNormalAtomicFact(InferNotNormalAtomicFactResult),
    NotEqualFact(InferNotEqualFactResult),
    NotLessFact(InferNotLessFactResult),
    NotGreaterFact(InferNotGreaterFactResult),
    NotLessEqualFact(InferNotLessEqualFactResult),
    NotGreaterEqualFact(InferNotGreaterEqualFactResult),
    NotIsSetFact(InferNotIsSetFactResult),
    NotIsNonemptySetFact(InferNotIsNonemptySetFactResult),
    NotIsFiniteSetFact(InferNotIsFiniteSetFactResult),
    NotInFact(InferNotInFactResult),
    NotIsCartFact(InferNotIsCartFactResult),
    NotIsTupleFact(InferNotIsTupleFactResult),
    NotSubsetFact(InferNotSubsetFactResult),
    NotSupersetFact(InferNotSupersetFactResult),
    FnEqualInFact(InferFnEqualInFactResult),
    NotFnEqualInFact(InferNotFnEqualInFactResult),
}

// NormalAtomicFact infer rules (mutually exclusive).
pub enum InferNormalAtomicFactResult {
    // Rule: concrete prop `$P(args)` exposes instantiated iff facts (one layer).
    ExpandDefinition(InferExpandDefinitionResult),
    NoInfer,
}

pub struct InferExpandDefinitionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

// InFact infer rules (mutually exclusive).
pub enum InferInFactResult {
    SetBuilder(InferSetBuilderMembershipProjectionResult),
    PowerSet(InferPowerSetMembershipProjectionResult),
    NoInfer,
}

pub struct InferSetBuilderMembershipProjectionResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferPowerSetMembershipProjectionResult {
    pub derived: Box<StoreFactAndInferResult>,
}

// Empty stubs: fill when the first infer rule for that shape exists.
pub struct InferLessFactResult {}
pub struct InferGreaterFactResult {}
pub struct InferLessEqualFactResult {}
pub struct InferGreaterEqualFactResult {}
pub struct InferIsSetFactResult {}
pub struct InferIsNonemptySetFactResult {}
pub struct InferIsFiniteSetFactResult {}
pub enum InferIsCartFactResult {
    // Rule: `$is_cart(C)` exposes `cart_dim(C) >= 2` (every cart has ≥2 factors).
    DimensionLowerBound(InferIsCartDimensionLowerBoundResult),
}

pub struct InferIsCartDimensionLowerBoundResult {
    pub derived: Box<StoreFactAndInferResult>,
}
pub struct InferIsTupleFactResult {}
pub struct InferSubsetFactResult {}
pub struct InferSupersetFactResult {}
pub struct InferNotNormalAtomicFactResult {}
pub struct InferNotEqualFactResult {}
pub struct InferNotLessFactResult {}
pub struct InferNotGreaterFactResult {}
pub struct InferNotLessEqualFactResult {}
pub struct InferNotGreaterEqualFactResult {}
pub struct InferNotIsSetFactResult {}
pub struct InferNotIsNonemptySetFactResult {}
pub struct InferNotIsFiniteSetFactResult {}
pub struct InferNotInFactResult {}
pub struct InferNotIsCartFactResult {}
pub struct InferNotIsTupleFactResult {}
pub struct InferNotSubsetFactResult {}
pub struct InferNotSupersetFactResult {}
pub struct InferFnEqualInFactResult {}
pub struct InferNotFnEqualInFactResult {}

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
            Self::EqualFact(r) => {
                let mut ids = Vec::new();
                if let Some(shape) = &r.cart_tuple_shape {
                    for d in &shape.derived {
                        ids.extend(d.stored_fact_ids());
                    }
                }
                ids
            }
            Self::ExceptEquality(r) => r.stored_fact_ids(),
        }
    }
}

impl InferAtomicExceptEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::NormalAtomicFact(r) => r.stored_fact_ids(),
            Self::InFact(r) => r.stored_fact_ids(),
            Self::IsCartFact(r) => r.stored_fact_ids(),
            Self::LessFact(_)
            | Self::GreaterFact(_)
            | Self::LessEqualFact(_)
            | Self::GreaterEqualFact(_)
            | Self::IsSetFact(_)
            | Self::IsNonemptySetFact(_)
            | Self::IsFiniteSetFact(_)
            | Self::IsTupleFact(_)
            | Self::SubsetFact(_)
            | Self::SupersetFact(_)
            | Self::NotNormalAtomicFact(_)
            | Self::NotEqualFact(_)
            | Self::NotLessFact(_)
            | Self::NotGreaterFact(_)
            | Self::NotLessEqualFact(_)
            | Self::NotGreaterEqualFact(_)
            | Self::NotIsSetFact(_)
            | Self::NotIsNonemptySetFact(_)
            | Self::NotIsFiniteSetFact(_)
            | Self::NotInFact(_)
            | Self::NotIsCartFact(_)
            | Self::NotIsTupleFact(_)
            | Self::NotSubsetFact(_)
            | Self::NotSupersetFact(_)
            | Self::FnEqualInFact(_)
            | Self::NotFnEqualInFact(_) => Vec::new(),
        }
    }
}

impl InferIsCartFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::DimensionLowerBound(r) => r.derived.stored_fact_ids(),
        }
    }
}

impl InferNormalAtomicFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::ExpandDefinition(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::NoInfer => Vec::new(),
        }
    }
}

impl InferInFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::SetBuilder(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::PowerSet(r) => r.derived.stored_fact_ids(),
            Self::NoInfer => Vec::new(),
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
