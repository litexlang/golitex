use crate::new_pipeline::ast::fact::{
    AndFact, AtomicFact, ChainFact, ExistShapedFact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::runtime::FactId;

// What store_fact wrote into the current top ExecEnv (index only).
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

// What infer_fact derived from an already-stored fact.
pub enum InferFactResult {
    // No extra evidence fields; side effects may still have run.
    Empty,
    ChainFact {
        transitive_closures: Vec<StoreChainTransitiveClosureResult>,
    },
    NotForallFact {
        derived_exist: StoreExistShapedFactResult,
    },
}

// Mirror of store_fact then infer_fact. ExecEnv remains authoritative.
pub enum StoreFactAndInferResult {
    AtomicFact(StoreAtomicFactResult),
    AndFact(StoreAndFactResult),
    ChainFact(StoreChainFactResult),
    OrFact(StoreOrFactResult),
    ExistShapedFact(StoreExistShapedFactResult),
    NotForallFact(StoreNotForallFactResult),
    ForallFact(StoreForallFactResult),
    ForallFactWithIff(StoreForallFactWithIffResult),
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

// Store-only chain: whole + adjacent edges (no transitive closures).
pub struct StoreChainFactStorePart {
    pub whole_fact_id: FactId,
    pub fact: ChainFact,
    pub adjacent: Vec<StoreChainAdjacentResult>,
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
pub struct StoreExistShapedFactResult {
    pub whole_fact_id: FactId,
    pub fact: ExistShapedFact,
}

// Store-only not-forall (counterexample exist is infer).
pub struct StoreNotForallFactStorePart {
    pub whole_fact_id: FactId,
    pub fact: NotForallFact,
}

// Record not-forall, and store its De Morgan counterexample exist into known_exist.
pub struct StoreNotForallFactResult {
    pub whole_fact_id: FactId,
    pub fact: NotForallFact,
    pub derived_exist: StoreExistShapedFactResult,
}

// Record forall into facts_by_id and project then-conclusions into known_forall.
pub struct StoreForallFactResult {
    pub fact_id: FactId,
    pub fact: ForallFact,
}

// Split forall-iff into two forall directions, store each, keep surface id as primary.
pub struct StoreForallFactWithIffResult {
    pub fact_id: FactId,
    pub fact: ForallFactWithIff,
    pub forward: StoreForallFactResult,
    pub reverse: StoreForallFactResult,
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
            Self::ExistShapedFact(r) => r.whole_fact_id,
            Self::NotForallFact(r) => r.whole_fact_id,
            Self::ForallFact(r) => r.fact_id,
            Self::ForallFactWithIff(r) => r.fact_id,
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
            Self::ExistShapedFact(r) => vec![r.whole_fact_id],
            Self::NotForallFact(r) => {
                let mut ids = vec![r.whole_fact_id];
                ids.push(r.derived_exist.whole_fact_id);
                ids
            }
            Self::ForallFact(r) => vec![r.fact_id],
            // Surface iff id is primary; env records the two generated foralls.
            Self::ForallFactWithIff(r) => {
                vec![r.forward.fact_id, r.reverse.fact_id]
            }
        }
    }
}

pub(crate) fn merge_store_and_infer(
    stored: StoreFactResult,
    inferred: InferFactResult,
) -> StoreFactAndInferResult {
    match (stored, inferred) {
        (StoreFactResult::AtomicFact(r), InferFactResult::Empty) => {
            StoreFactAndInferResult::AtomicFact(r)
        }
        (StoreFactResult::AndFact(r), InferFactResult::Empty) => StoreFactAndInferResult::AndFact(r),
        (
            StoreFactResult::ChainFact(store_part),
            InferFactResult::ChainFact {
                transitive_closures,
            },
        ) => StoreFactAndInferResult::ChainFact(StoreChainFactResult {
            whole_fact_id: store_part.whole_fact_id,
            fact: store_part.fact,
            adjacent: store_part.adjacent,
            transitive_closures,
        }),
        (StoreFactResult::ChainFact(store_part), InferFactResult::Empty) => {
            StoreFactAndInferResult::ChainFact(StoreChainFactResult {
                whole_fact_id: store_part.whole_fact_id,
                fact: store_part.fact,
                adjacent: store_part.adjacent,
                transitive_closures: Vec::new(),
            })
        }
        (StoreFactResult::OrFact(r), InferFactResult::Empty) => StoreFactAndInferResult::OrFact(r),
        (StoreFactResult::ExistShapedFact(r), InferFactResult::Empty) => {
            StoreFactAndInferResult::ExistShapedFact(r)
        }
        (
            StoreFactResult::NotForallFact(store_part),
            InferFactResult::NotForallFact { derived_exist },
        ) => StoreFactAndInferResult::NotForallFact(StoreNotForallFactResult {
            whole_fact_id: store_part.whole_fact_id,
            fact: store_part.fact,
            derived_exist,
        }),
        (StoreFactResult::ForallFact(r), InferFactResult::Empty) => {
            StoreFactAndInferResult::ForallFact(r)
        }
        (StoreFactResult::ForallFactWithIff(r), InferFactResult::Empty) => {
            StoreFactAndInferResult::ForallFactWithIff(r)
        }
        _ => panic!("store_fact / infer_fact result shape mismatch"),
    }
}
