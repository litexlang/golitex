mod atomic;
mod composite;
mod quantified;
mod support;
mod types;
mod validation;

pub use atomic::core::*;
pub use composite::conjunction_and_chain::{
    AndChainAtomicFact, AndFact, ChainAtomicFact, ChainFact,
};
pub use composite::disjunction::OrFact;
pub use composite::quantifier_free::QuantifierFreeFact;
pub use quantified::existential::{ExistFactEnum, ExistentialSpec};
pub use quantified::universal::ForallFact;
pub use quantified::universal_iff::ForallFactWithIff;
pub use validation::fact_parameters::{
    check_exist_fact_has_no_duplicate_exist_free_parameter,
    check_forall_fact_has_no_duplicate_forall_free_parameter,
    check_forall_fact_with_iff_has_no_duplicate_forall_free_parameter,
};
pub use validation::object_parameters::{
    check_anonymous_fn_has_no_duplicate_fn_set_free_parameter,
    check_fn_set_has_no_duplicate_fn_set_free_parameter,
    check_set_builder_has_no_duplicate_set_builder_free_parameter,
};

pub use quantified::nested::ExistOrAndChainAtomicFact;
pub use types::{Fact, NotForallFact};
