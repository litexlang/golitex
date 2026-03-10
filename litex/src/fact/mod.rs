mod atomic_fact;
mod exist_fact;
mod forall_fact;
mod forall_fact_with_iff;
mod matchable_fact_with_atomic_fact_inside;
mod or_fact;
mod or_fact_or_and_fact_or_specific_fact;
mod reversible_fact;
mod specific_fact;

pub use atomic_fact::*;
pub use exist_fact::{ExistFact, FactInsideExistFact, NotExistFact, TrueExistFact};
pub use matchable_fact_with_atomic_fact_inside::{AndAtomicFact, ChainAtomicFact, MatchableFactWithAtomicFactInside};
pub use forall_fact::ForallFact;
pub use forall_fact_with_iff::ForallFactWithIff;
pub use or_fact::OrFact;
pub use or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
pub use specific_fact::SpecFact;

pub use fact_enum::Fact;
mod fact_enum;
