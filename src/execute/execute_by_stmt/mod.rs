mod builtin_thm;
mod exec_by_cases_stmt;
mod exec_by_contra_stmt;
mod exec_by_def_stmt;
mod exec_by_induc_stmt;
mod recover_induction_param;
mod exec_by_extension_stmt;
mod exec_by_fn_extension_stmt;
mod exec_by_enumerate_finite_set_stmt;
mod exec_by_for_stmt;
mod exec_expand_range_stmt;
mod exec_by_thm_stmt;
mod exec_by_regularity_axiom_stmt;
mod exec_by_axiom_of_choice_stmt;
mod exec_by_zorn_lemma_stmt;
mod helper;
mod negate_fact_for_contra;
mod negate_unique_exist;
mod negate_forall_iff;
mod enumerate_helpers;
mod enumerate_forall;
mod result;

pub use exec_by_cases_stmt::exec_by_cases_stmt;
pub use exec_by_contra_stmt::exec_by_contra_stmt;
pub use exec_by_def_stmt::exec_by_def_stmt;
pub use exec_by_induc_stmt::{exec_by_induc_stmt, exec_by_strong_induc_stmt};
pub use exec_by_extension_stmt::exec_by_extension_stmt;
pub use exec_by_fn_extension_stmt::exec_by_fn_extension_stmt;
pub use exec_by_enumerate_finite_set_stmt::exec_by_enumerate_finite_set_stmt;
pub use exec_by_for_stmt::exec_by_for_stmt;
pub use exec_expand_range_stmt::exec_expand_range_stmt;
pub use exec_by_thm_stmt::{exec_by_thm_stmt, exec_release_thm_stmt};
pub use exec_by_regularity_axiom_stmt::exec_release_regularity_axiom_stmt;
pub use exec_by_axiom_of_choice_stmt::exec_release_axiom_of_choice_stmt;
pub use exec_by_zorn_lemma_stmt::exec_release_zorn_lemma_stmt;
pub use result::{
    EnumerateAssignmentSuccess, EnumerateAssignmentOutcome,
    ByInducBodySuccess, ByInducCaseFailed, ByInducCaseSuccess, ExecByCasesStmtResult, ExecByContraStmtResult,
    ExecByDefStmtResult, ExecByEnumerateFiniteSetStmtResult, ExecByExtensionStmtResult,
    ExecByFnExtensionStmtResult, ExecByForStmtResult, ExecByInducStmtFailed, ExecByInducStmtResult, ExecByStmtResult,
    ExecByStrongInducStmtFailed, ExecByStrongInducStmtResult, ExecByThmStmtResult, ExecExpandRangeStmtResult,
    ExecReleaseAxiomOfChoiceStmtResult, ExecReleaseRegularityAxiomStmtResult,
    BuiltinThmApplication, ExecByThmStmtFailed, ExecReleaseThmStmtFailed, ExecReleaseThmStmtResult, ExecReleaseZornLemmaStmtResult,
};
pub(crate) use exec_by_thm_stmt::{prepare_release_conclusions, PreparedRelease};
pub(crate) use result::{ByContradictionClosingFailed, ExecByContraStmtFailed};
// Existing failure IR consumed by the crate's Normal/Detailed JSON projection.
pub(crate) use result::{ByCasesBranchFailed, ExecByCasesStmtFailed, ExecByExtensionStmtFailed};
pub(crate) use result::ExecByFnExtensionStmtFailed;
pub(crate) use helper::{
    proof_verify_state, store_goal_fact, verify_goal_fact,
};

#[cfg(test)]
#[path = "../../../tests/unit/execute/showcase_regressions/tests.rs"]
mod showcase_regressions;
