mod atomic_fact;
mod chain_fact_order_closure;
mod check_fact_has_no_duplicate_free_parameter;
mod exist_fact;
mod fact_inside_forall;
mod forall_fact;
mod forall_fact_with_iff;
mod mark_forall_param_coverage;
mod matchable_fact_with_atomic_fact_inside;
mod or_and_chain_atomic_fact;
mod or_fact;
pub use atomic_fact::*;
pub use check_fact_has_no_duplicate_free_parameter::{
    check_exist_fact_has_no_duplicate_exist_free_parameter,
    check_forall_fact_has_no_duplicate_forall_free_parameter,
};
pub use exist_fact::{ExistFactBody, ExistFactEnum};
pub use forall_fact::ForallFact;
pub use forall_fact_with_iff::ForallFactWithIff;
pub use matchable_fact_with_atomic_fact_inside::{
    AndChainAtomicFact, AndFact, ChainAtomicFact, ChainFact,
};
pub use or_and_chain_atomic_fact::OrAndChainAtomicFact;
pub use or_fact::OrFact;

pub use fact::{Fact, NotForallFact};
mod fact;
pub use fact_inside_forall::ExistOrAndChainAtomicFact;
