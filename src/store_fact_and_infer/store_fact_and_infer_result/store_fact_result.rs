use crate::ast::fact::{
    AndFact, AtomicFact, ChainFact, ExistShapedFact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::runtime::FactId;

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
