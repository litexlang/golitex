mod atomic_fact;
mod atomic_fact_args;
mod atomic_fact_from;
mod atomic_fact_metadata;
mod chain_fact_order_closure;
mod check_fact_has_no_duplicate_free_parameter;
mod check_obj_has_no_duplicate_free_parameter;
mod exist_fact;
mod fact_inside_forall;
mod forall_fact;
mod forall_fact_with_iff;
mod helper;
mod mark_forall_param_coverage;
mod matchable_fact_with_atomic_fact_inside;
mod or_fact;
mod quantifier_free_fact;
pub use atomic_fact::*;
pub use check_fact_has_no_duplicate_free_parameter::{
    check_exist_fact_has_no_duplicate_exist_free_parameter,
    check_forall_fact_has_no_duplicate_forall_free_parameter,
    check_forall_fact_with_iff_has_no_duplicate_forall_free_parameter,
    check_quantifier_free_fact_has_no_duplicate_free_parameter,
};
pub use check_obj_has_no_duplicate_free_parameter::{
    check_anonymous_fn_has_no_duplicate_fn_set_free_parameter,
    check_fn_set_has_no_duplicate_fn_set_free_parameter,
    check_set_builder_has_no_duplicate_set_builder_free_parameter,
};
pub use exist_fact::{ExistFactEnum, ExistentialSpec};
pub use forall_fact::ForallFact;
pub use forall_fact_with_iff::ForallFactWithIff;
pub use matchable_fact_with_atomic_fact_inside::{
    AndChainAtomicFact, AndFact, ChainAtomicFact, ChainFact,
};
pub use or_fact::OrFact;
pub use quantifier_free_fact::QuantifierFreeFact;

pub use fact::{Fact, NotForallFact};
mod fact;
pub use fact_inside_forall::ExistOrAndChainAtomicFact;
