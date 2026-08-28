//! Fact storage and output classification.

use crate::prelude::*;

impl Fact {
    pub fn store_reason() -> &'static str {
        "proved statement"
    }

    pub fn fact_type_string(&self) -> String {
        match self {
            Fact::AtomicFact(_) => "AtomicFact".to_string(),
            Fact::ExistFact(_) => "ExistFact".to_string(),
            Fact::OrFact(_) => "OrFact".to_string(),
            Fact::AndFact(_) => "AndFact".to_string(),
            Fact::ChainFact(_) => "ChainFact".to_string(),
            Fact::ForallFact(_) => "ForallFact".to_string(),
            Fact::ForallFactWithIff(_) => "ForallFactWithIff".to_string(),
            Fact::NotForall(_) => "NotForallFact".to_string(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            Fact::AtomicFact(atomic_fact) => atomic_fact.output_type_string(),
            Fact::ExistFact(exist_fact) => match exist_fact {
                ExistFactEnum::ExistFact(_) => "existence fact".to_string(),
                ExistFactEnum::ExistUniqueFact(_) => "unique existence fact".to_string(),
                ExistFactEnum::NotExistFact(_) => "nonexistence fact".to_string(),
            },
            Fact::OrFact(_) => "disjunction fact".to_string(),
            Fact::AndFact(_) => "conjunction fact".to_string(),
            Fact::ChainFact(_) => "calculation chain".to_string(),
            Fact::ForallFact(_) => "universal fact".to_string(),
            Fact::ForallFactWithIff(_) => "universal equivalence fact".to_string(),
            Fact::NotForall(_) => "negated universal fact".to_string(),
        }
    }
}
