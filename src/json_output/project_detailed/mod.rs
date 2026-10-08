//! Detailed JSON projection: field-isomorphic Exec/Verify IR (no `local_env`).

mod aggregate_evaluation;
mod aggregate_identity;
mod atomic_builtin_rewrite;
mod builtin_atomic_gen;
mod entry;
mod equality_builtin_gen;
mod exist_builtin_gen;
mod function_domain;
mod induction;
mod known_special_property;
mod known_tuple;
mod or_builtin_gen;
mod reduce_rules;
mod register;
mod searched;
mod stmt;
mod store;
mod strategy_gen;
mod theorem;
mod verify;
mod wd;
mod wd_by_def;
mod wd_failure;

pub use entry::project_run_detailed;
pub(in crate::json_output) use induction::{
    project_induc_definition_failure, project_induc_failure, project_strong_induc_failure,
};
pub use stmt::project_stmt_detailed;

pub(in crate::json_output) use theorem::{
    project_by_thm_failure, project_def_thm_failure, project_release_thm_failure,
};

pub(in crate::json_output) use stmt::{project_cases_definition_failure, project_def_prop_failure};
pub(in crate::json_output) use verify::project_verify_fact;
pub(in crate::json_output) use wd::project_verify_equal_wd;
pub(in crate::json_output) use wd::project_verify_obj_wd;

mod closed_calculation;

mod structural_membership;

mod witness_failure;

mod proof_block_failure;
pub(in crate::json_output) use proof_block_failure::{
    project_cases_failure, project_claim_failure, project_contra_failure, project_extension_failure,
};

mod function_body;
mod template_failure;
pub(in crate::json_output) use template_failure::project_template_failure;

mod log_algebra_base;

pub(in crate::json_output) use stmt::{project_release_cart_def, project_release_tuple_def};
