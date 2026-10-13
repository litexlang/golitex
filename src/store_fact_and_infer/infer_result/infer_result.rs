use super::*;
use crate::runtime::FactId;

pub enum InferResult {
    AtomicFact(InferAtomicFactResult),
    ExistFact(InferPlainExistFactResult),
    ExistUniqueFact(InferExistUniqueFactResult),
    NotExistFact(InferNotExistFactResult),
    OrFact(InferOrFactResult),
    AndFact(InferAndFactResult),
    ChainFact(InferChainFactResult),
    ForallFact(InferForallFactResult),
    ForallFactWithIff(InferForallFactWithIffResult),
    NotForall(InferNotForallFactResult),
}

impl InferResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::AtomicFact(r) => r.stored_fact_ids(),
            Self::AndFact(r) => r
                .components
                .iter()
                .flat_map(|c| c.stored_fact_ids())
                .collect(),
            Self::ChainFact(r) => r
                .adjacent_infers
                .iter()
                .flat_map(|e| e.infer.stored_fact_ids())
                .chain(
                    r.transitive_closures
                        .iter()
                        .flat_map(|c| c.derived.stored_fact_ids()),
                )
                .collect(),
            Self::ExistFact(_)
            | Self::OrFact(_)
            | Self::ForallFact(_)
            | Self::ForallFactWithIff(_) => Vec::new(),
            Self::ExistUniqueFact(r) => match r {
                InferExistUniqueFactResult::UniquenessForall(p) => p.derived.stored_fact_ids(),
                InferExistUniqueFactResult::NoInfer => Vec::new(),
            },
            Self::NotExistFact(r) => match r {
                InferNotExistFactResult::DemorganForall(p) => p.derived.stored_fact_ids(),
                InferNotExistFactResult::NoInfer => Vec::new(),
            },
            Self::NotForall(r) => r.derived_exist.stored_fact_ids(),
        }
    }
}
