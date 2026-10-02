//! Detailed JSON projection: field-isomorphic Exec/Verify IR (no `local_env`).

mod builtin_atomic_gen;
mod entry;
mod induction;
mod equality_builtin_gen;
mod aggregate_evaluation;
mod aggregate_identity;
mod exist_builtin_gen;
mod or_builtin_gen;
mod searched;
mod known_special_property;
mod known_tuple;
mod stmt;
mod theorem;
mod store;
mod strategy_gen;
mod verify;
mod wd;
mod wd_failure;
mod wd_by_def;

pub use entry::{project_run_detailed, project_stmt_detailed};
pub(in crate::json_output) use induction::{project_induc_failure, project_strong_induc_failure, project_induc_definition_failure};

pub(in crate::json_output) use theorem::{project_release_thm_failure, project_by_thm_failure, project_def_thm_failure};

pub(in crate::json_output) use wd::project_verify_obj_wd;
