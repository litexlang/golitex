#[path = "atomic/core.rs"]
mod atomic_core;
#[path = "atomic/transparent_definition.rs"]
mod atomic_transparent_definition;
#[path = "proof_search/builtin_rule_state.rs"]
mod builtin_rule_state;
#[path = "equality/core.rs"]
mod equality_core;
#[path = "proof_search/universal_profile.rs"]
pub mod known_forall_profile;
#[path = "quantified/negated_existential.rs"]
mod not_exist_demorgan_forall;
#[path = "composite/conjunction_and_chain.rs"]
mod verify_and_chain_fact;
#[path = "atomic/definition.rs"]
mod verify_atomic_fact_by_definition;
#[path = "atomic/universal_search.rs"]
mod verify_atomic_fact_with_known_forall;
#[path = "proof_search/builtin_rule.rs"]
mod verify_builtin_rule;
mod verify_builtin_rules;
mod verify_builtin_strategies;
#[path = "proof_search/builtin_strategy.rs"]
mod verify_builtin_strategy;
#[path = "proof_search/explicit_syntax.rs"]
mod verify_by_syntax;
#[path = "dispatch.rs"]
mod verify_dispatch;
#[path = "equality/patterns.rs"]
mod verify_equality_by_builtin_rules;
#[path = "quantified/existential.rs"]
mod verify_exist_fact;
#[path = "quantified/existential_search.rs"]
mod verify_exist_fact_with_known_forall;
#[path = "well_definedness/fact.rs"]
mod verify_fact_well_defined;
#[path = "support/argument_matching.rs"]
mod verify_facts_the_same_type_and_return_matched_args;
#[path = "equality/function.rs"]
mod verify_fn_equal_in_builtin;
#[path = "equality/function_set.rs"]
mod verify_fn_set_equality_builtin_rule;
#[path = "quantified/universal.rs"]
mod verify_forall_fact;
#[path = "quantified/universal_iff.rs"]
mod verify_forall_fact_with_iff;
#[path = "atomic/function_properties.rs"]
mod verify_function_properties_builtin;
#[path = "support/helper.rs"]
mod verify_helper;
pub use verify_helper::nested_obj_binder_normalized_fact_key;
#[path = "atomic/non_equational.rs"]
mod atomic_non_equational;
#[path = "atomic/known_facts.rs"]
mod verify_known_atomic_facts;
#[path = "quantified/not_universal.rs"]
mod verify_not_forall_fact;
pub use verify_builtin_rules::{
    choice_function_for_definition_facts, choice_function_for_fact,
    general_cart_member_choice_fact, general_cart_member_fn_set,
    verify_choice_function_for_arg_types,
};
pub use verify_builtin_rules::{
    compare_normalized_number_str_to_zero, compare_number_strings, NumberCompareResult,
};
#[path = "support/parameter_requirements.rs"]
mod verify_arg_satisfy_param_def;
#[path = "atomic/function_membership.rs"]
mod verify_fn_membership_by_definition;
#[path = "atomic/numeric_membership.rs"]
mod verify_number_in_standard_set;
#[path = "well_definedness/object.rs"]
mod verify_obj_well_defined;
#[path = "composite/disjunction.rs"]
mod verify_or_fact;
#[path = "composite/disjunction_search.rs"]
mod verify_or_fact_with_known_forall;
#[path = "atomic/set_relations.rs"]
pub mod verify_proper_set_relations_builtin;
#[path = "proof_search/context_state.rs"]
mod verify_state;
#[path = "well_definedness/local_environment.rs"]
mod verify_well_defined_in_local_env;

pub use verify_number_in_standard_set::number_is_in_c_star;
pub use verify_number_in_standard_set::number_is_in_n;
pub use verify_number_in_standard_set::number_is_in_n_pos;
pub use verify_number_in_standard_set::number_is_in_q_neg;
pub use verify_number_in_standard_set::number_is_in_q_pos;
pub use verify_number_in_standard_set::number_is_in_q_star;
pub use verify_number_in_standard_set::number_is_in_r_neg;
pub use verify_number_in_standard_set::number_is_in_r_pos;
pub use verify_number_in_standard_set::number_is_in_r_star;
pub use verify_number_in_standard_set::number_is_in_z;
pub use verify_number_in_standard_set::number_is_in_z_neg;
pub use verify_number_in_standard_set::number_is_in_z_star;

pub use atomic_non_equational::AlternateFactSearch;
pub use builtin_rule_state::BuiltinRuleSearchState;
pub use verify_state::VerifyState;
