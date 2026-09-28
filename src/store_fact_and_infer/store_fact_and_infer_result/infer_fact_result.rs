use crate::ast::names::AtomicName;
use crate::runtime::FactId;

use super::{InferAtomicFactResult, StoreFactAndInferResult};

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
