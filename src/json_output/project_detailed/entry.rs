//! Entry points for Detailed JSON projection.

use super::store::{project_have_store_ids, project_store_and_infer};
use super::stmt::project_stmt_detailed;
use super::verify::project_verify_fact;
use super::wd::{project_param_type_wd, project_verify_obj_wd};
use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    VerifyAtomicExceptEqualityFactFailed, VerifyAtomicExceptEqualityFactResult,
    VerifyEqualityFailed, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyFactResult};
use crate::execute::{
    ExecHaveObjEqualStmtResult, ExecHaveObjInNonemptySetStmtFailed,
    ExecHaveObjInNonemptySetStmtResult, ParamTypeFactCheckResult,
};
use crate::json_output::helper::{bool_value, object_for, string};
use crate::json_output::project_normal::OutputDetail;
use crate::knowledge_base::JsonValue;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;
use std::path::Path;

pub fn project_run_detailed(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let statement_results: Vec<JsonValue> = run
        .statement_results
        .iter()
        .map(|stmt| project_stmt_detailed(stmt, runtime))
        .collect();
    let path_value = match path {
        Some(p) => string(p.display().to_string()),
        None => JsonValue::Null,
    };
    let session_error = match &run.session_error {
        None => JsonValue::Null,
        Some(err) => string(format!("{err:?}")),
    };
    object_for(runtime, vec![
        ("kind", string("run")),
        ("success", bool_value(run.success)),
        ("target", string(target)),
        ("path", path_value),
        ("detail", string(OutputDetail::Detailed.as_str())),
        (
            "language",
            string(runtime.launch_command.output_language().as_str()),
        ),
        ("statement_results", JsonValue::Array(statement_results)),
        ("session_error", session_error),
    ])
}

pub(super) fn project_fact_only(fact: &ExecFactStmtResult, runtime: &Runtime) -> JsonValue {
    match fact {
        ExecFactStmtResult::Success(success) => object_for(runtime, vec![
            ("success", bool_value(true)),
            ("kind", string("fact")),
            (
                "statement",
                string(verify_goal_display(&success.verify_result)),
            ),
            (
                "verify",
                project_verify_fact(&success.verify_result, runtime),
            ),
            (
                "store_and_infer",
                project_store_and_infer(&success.store_and_infer_result, runtime),
            ),
        ]),
        ExecFactStmtResult::Failed(verify) => object_for(runtime, vec![
            ("success", bool_value(false)),
            ("kind", string("fact")),
            ("statement", string(verify_goal_display(verify))),
            ("verify", project_verify_fact(verify, runtime)),
            (
                "store_and_infer",
                object_for(runtime, vec![
                    ("stores", JsonValue::Array(Vec::new())),
                    ("infers", JsonValue::Array(Vec::new())),
                ]),
            ),
        ]),
    }
}

pub(super) fn project_have_in_nonempty_only(
    have: &ExecHaveObjInNonemptySetStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    match have {
        ExecHaveObjInNonemptySetStmtResult::Success(success) => object_for(runtime, vec![
            ("success", bool_value(true)),
            ("kind", string("have_obj_in_nonempty_set")),
            ("statement", string(success.statement.readable_string())),
            (
                "param_type_well_defined",
                JsonValue::Array(
                    success
                        .groups
                        .iter()
                        .map(|g| project_param_type_wd(&g.param_type_well_defined, runtime))
                        .collect(),
                ),
            ),
            (
                "nonempty_checks",
                JsonValue::Array(
                    success
                        .groups
                        .iter()
                        .map(|g| project_param_type_fact_check(&g.nonempty_check, runtime))
                        .collect(),
                ),
            ),
            (
                "store_and_infer",
                project_have_store_ids(&success.store_and_infer_result.stored_fact_ids, runtime),
            ),
        ]),
        ExecHaveObjInNonemptySetStmtResult::Failed(failed) => object_for(runtime, vec![
            ("success", bool_value(false)),
            ("kind", string("have_obj_in_nonempty_set")),
            ("why_failed", project_have_in_failed(failed, runtime)),
            (
                "store_and_infer",
                object_for(runtime, vec![
                    ("stores", JsonValue::Array(Vec::new())),
                    ("infers", JsonValue::Array(Vec::new())),
                ]),
            ),
        ]),
    }
}

pub(super) fn project_have_equal_only(
    have: &ExecHaveObjEqualStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    match have {
        ExecHaveObjEqualStmtResult::Success(success) => object_for(runtime, vec![
            ("success", bool_value(true)),
            ("kind", string("have_obj_equal")),
            ("statement", string(success.statement.readable_string())),
            (
                "param_type_well_defined",
                JsonValue::Array(
                    success
                        .type_preflight.param_type_well_defined
                        .iter()
                        .map(|p| project_param_type_wd(p, runtime))
                        .collect(),
                ),
            ),
            (
                "equal_to_well_defined",
                JsonValue::Array(
                    success
                        .equal_to_well_defined
                        .iter()
                        .map(|w| project_verify_obj_wd(w, runtime))
                        .collect(),
                ),
            ),
            (
                "membership_checks",
                JsonValue::Array(
                    success
                        .membership_checks
                        .iter()
                        .map(|v| project_verify_fact(v, runtime))
                        .collect(),
                ),
            ),
            (
                "store_and_infer",
                project_have_store_ids(&success.store_and_infer_result.stored_fact_ids, runtime),
            ),
        ]),
        ExecHaveObjEqualStmtResult::Failed(_) => object_for(runtime, vec![
            ("success", bool_value(false)),
            ("kind", string("have_obj_equal")),
            (
                "why_failed",
                object_for(runtime, vec![("phase", string("have_obj_equal"))]),
            ),
            (
                "store_and_infer",
                object_for(runtime, vec![
                    ("stores", JsonValue::Array(Vec::new())),
                    ("infers", JsonValue::Array(Vec::new())),
                ]),
            ),
        ]),
    }
}

fn project_have_in_failed(
    failed: &ExecHaveObjInNonemptySetStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    match failed {
        ExecHaveObjInNonemptySetStmtFailed::ParamType(wd) => object_for(runtime, vec![
            ("phase", string("param_type")),
            ("well_defined", project_verify_obj_wd(wd, runtime)),
        ]),
        ExecHaveObjInNonemptySetStmtFailed::NonemptyCheck(v) => object_for(runtime, vec![
            ("phase", string("nonempty_check")),
            ("verify", project_verify_fact(v, runtime)),
        ]),
        ExecHaveObjInNonemptySetStmtFailed::AutoOpenStructLayer(_) => {
            object_for(runtime, vec![("phase", string("auto_open_struct_layer"))])
        }
    }
}

fn project_param_type_fact_check(
    check: &ParamTypeFactCheckResult,
    runtime: &Runtime,
) -> JsonValue {
    match check {
        ParamTypeFactCheckResult::Set => object_for(runtime, vec![("type", string("set"))]),
        ParamTypeFactCheckResult::NonemptySet => object_for(runtime, vec![("type", string("nonempty_set"))]),
        ParamTypeFactCheckResult::FiniteSet => object_for(runtime, vec![("type", string("finite_set"))]),
        ParamTypeFactCheckResult::Obj(v) => object_for(runtime, vec![
            ("type", string("obj")),
            ("verify", project_verify_fact(v, runtime)),
        ]),
    }
}

fn verify_goal_display(verify: &VerifyFactResult) -> String {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(s) => s.fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToSearchProof { fact, .. },
            ) => fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(_),
            ) => "<wd_failed>".into(),
        },
        VerifyFactResult::Equality(r) => match r.as_ref() {
            VerifyEqualityResult::Success(s) => {
                AtomicFact::EqualFact(s.fact.clone()).readable_string()
            }
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof { fact, .. }) => {
                AtomicFact::EqualFact(fact.clone()).readable_string()
            }
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_)) => {
                "<wd_failed>".into()
            }
        },
        _ => super::super::project_normal::verify_goal_display(verify),
    }
}
