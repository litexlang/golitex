mod atomic;
mod classification;
mod composite;
mod display;
mod fact;
mod fact_conversions;
pub mod forall_conclusion_location;
pub mod id;
mod not_forall;
mod quantified;
mod source_location;
mod support;
mod validation;

pub use atomic::*;
pub use composite::conjunction_and_chain::{
    AndChainAtomicFact, AndFact, ChainAtomicFact, ChainFact,
};
pub use composite::disjunction::OrFact;
pub use composite::order_closure::NumericOrderChainClosureStep;
pub use composite::quantifier_free::QuantifierFreeFact;
pub use quantified::existential::{ExistFact, PlainExistFact};
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

pub use fact::Fact;
pub use not_forall::NotForallFact;
pub use quantified::nested::ExistOrAndChainAtomicFact;
