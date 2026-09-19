use crate::new_pipeline::ast::fact::{AndFact, AtomicFact, ChainFact, ExistFactFamily, NotForallFact, OrFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::runtime::FactId;

// Mirror of what store_fact_and_infer wrote into the current top ExecEnv.
// ExecEnv remains authoritative; this is stage-ordered replay evidence.
pub enum StoreFactAndInferResult {
    AtomicFact(StoreAtomicFactResult),
    AndFact(StoreAndFactResult),
    ChainFact(StoreChainFactResult),
    OrFact(StoreOrFactResult),
    ExistFact(StoreExistFactResult),
    NotForallFact(StoreNotForallFactResult),
    // Forall / forall-iff until specialized store pipelines exist.
    RecordedFact { fact_id: FactId },
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

pub struct StoreChainFactResult {
    pub whole_fact_id: FactId,
    pub fact: ChainFact,
    pub adjacent: Vec<StoreChainAdjacentResult>,
    // Empty when polarity breaks or the predicate is not transitive.
    pub transitive_closures: Vec<StoreChainTransitiveClosureResult>,
}

pub struct StoreChainAdjacentResult {
    pub edge_index: usize,
    pub fact_id: FactId,
    pub fact: AtomicFact,
}

// Whole or only; branches are not projected into known-atomic indexes.
pub struct StoreOrFactResult {
    pub whole_fact_id: FactId,
    pub fact: OrFact,
}

// Whole exist only; body clauses are not projected into known-atomic indexes.
pub struct StoreExistFactResult {
    pub whole_fact_id: FactId,
    pub fact: ExistFactFamily,
}

// Record not-forall, and store its De Morgan counterexample exist into known_exist.
pub struct StoreNotForallFactResult {
    pub whole_fact_id: FactId,
    pub fact: NotForallFact,
    pub derived_exist: StoreExistFactResult,
}

pub struct StoreChainTransitiveClosureResult {
    pub cite: ChainTransitiveCite,
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premise_edge_indexes: Vec<usize>,
    pub conclusion: AtomicFact,
    pub conclusion_fact_id: FactId,
}

// Provenance of a stored non-adjacent chain consequence.
pub enum ChainTransitiveCite {
    BuiltinEquality,
    BuiltinNumericOrder,
    KnownTransitive { prop_name: AtomicName },
}

impl StoreFactAndInferResult {
    // Whole fact written by this store step (and-root / or-root / atomic / …).
    pub fn primary_fact_id(&self) -> FactId {
        match self {
            Self::AtomicFact(r) => r.fact_id,
            Self::AndFact(r) => r.whole_fact_id,
            Self::ChainFact(r) => r.whole_fact_id,
            Self::OrFact(r) => r.whole_fact_id,
            Self::ExistFact(r) => r.whole_fact_id,
            Self::NotForallFact(r) => r.whole_fact_id,
            Self::RecordedFact { fact_id } => *fact_id,
        }
    }

    // Atomic pieces projected into known-atomic indexes (and/chain components).
    // Empty for or / exist / forall-shaped stores that only record the whole.
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
            | Self::ExistFact(_)
            | Self::NotForallFact(_)
            | Self::RecordedFact { .. } => Vec::new(),
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
                let mut ids =
                    Vec::with_capacity(1 + r.adjacent.len() + r.transitive_closures.len());
                ids.push(r.whole_fact_id);
                for a in &r.adjacent {
                    ids.push(a.fact_id);
                }
                for c in &r.transitive_closures {
                    ids.push(c.conclusion_fact_id);
                }
                ids
            }
            Self::OrFact(r) => vec![r.whole_fact_id],
            Self::ExistFact(r) => vec![r.whole_fact_id],
            Self::NotForallFact(r) => {
                let mut ids = vec![r.whole_fact_id];
                ids.push(r.derived_exist.whole_fact_id);
                ids
            }
            Self::RecordedFact { fact_id } => vec![*fact_id],
        }
    }
}
