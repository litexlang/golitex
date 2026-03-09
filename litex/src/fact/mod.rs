mod and_fact;
mod and_fact_or_specific_fact;
mod atomic_fact;
mod exist_fact;
mod forall_fact;
mod forall_fact_with_iff;
mod or_fact;
mod or_fact_or_and_fact_or_specific_fact;
mod reversible_fact;
mod specific_fact;

pub use and_fact::{AndFact, AndSpecFacts, ChainFact};
pub use and_fact_or_specific_fact::AndFactOrSpecFact;
pub use atomic_fact::*;
pub use exist_fact::{AndAtomicFact, ChainAtomicFact, ExistFact, FactInOrAtomicFact, FactInsideExistFact, NotExistFact, OrAtomicFact, TrueExistFact};
pub use forall_fact::ForallFact;
pub use forall_fact_with_iff::ForallFactWithIff;
pub use or_fact::OrFact;
pub use or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
pub use specific_fact::SpecFact;

pub use fact_enum::Fact;
mod fact_enum;
