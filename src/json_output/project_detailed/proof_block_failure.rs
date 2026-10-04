//! Mirror the existing failed proof stages without changing execution.
use super::verify::project_verify_fact;
use super::wd::project_verify_fact_wd_result;
use crate::execute::execute_by_stmt::{
    ByCasesBranchFailed, ByContradictionClosingFailed, ExecByCasesStmtFailed,
    ExecByContraStmtFailed, ExecByExtensionStmtFailed,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtFailed, ExecSketchStmtFailed, ProofBlockBodyFailed,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

fn message(phase: &str, text: &str, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![("phase", string(phase)), ("message", string(text))],
    )
}
fn verify(
    phase: &str,
    result: &crate::execute::execute_fact_stmt::VerifyFactResult,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", string(phase)),
            ("result", project_verify_fact(result, rt)),
        ],
    )
}
fn wd(
    result: &crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", string("goal_wd")),
            ("result", project_verify_fact_wd_result(result, rt)),
        ],
    )
}
fn index(value: usize) -> JsonValue {
    JsonValue::Number(value as f64)
}
fn body(failure: &ProofBlockBodyFailed, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", string("proof_body")),
            ("step_index", index(failure.step_index)),
            (
                "result",
                super::stmt::project_stmt_detailed(&failure.result, rt),
            ),
        ],
    )
}

pub(in crate::json_output) fn project_claim_failure(
    failure: &ExecClaimStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecClaimStmtFailed::*;
    match failure {
        GoalWd(result) => wd(result, rt),
        GoalUnsupported(text) => message("goal_unsupported", text, rt),
        Introduce(text) => message("introduce", text, rt),
        ProofBody(failure) => body(failure, rt),
        Conclusion { index: i, result } => object_for(
            rt,
            vec![
                ("phase", string("conclusion")),
                ("index", index(*i)),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
        Store(text) => message("store", text, rt),
    }
}

pub(in crate::json_output) fn project_sketch_failure(
    failure: &ExecSketchStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecSketchStmtFailed::ProofBody(failure) => body(failure, rt),
    }
}

pub(in crate::json_output) fn project_extension_failure(
    failure: &ExecByExtensionStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecByExtensionStmtFailed::*;
    match failure {
        GoalWd(result) => wd(result, rt),
        ProofBody(failure) => body(failure, rt),
        LeftToRight(result) => verify("left_to_right", result, rt),
        RightToLeft(result) => verify("right_to_left", result, rt),
        Store(text) => message("store", text, rt),
    }
}

pub(in crate::json_output) fn project_cases_failure(
    failure: &ExecByCasesStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecByCasesStmtFailed::*;
    match failure {
        LengthMismatch(text) => message("length_mismatch", text, rt),
        ThenFactWd { index: i, result } => object_for(
            rt,
            vec![
                ("phase", string("then_fact_wd")),
                ("index", index(*i)),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        ),
        Coverage(result) => verify("coverage", result, rt),
        Branch { index: i, failed } => object_for(
            rt,
            vec![
                ("phase", string("branch")),
                ("index", index(*i)),
                ("failure", branch(failed, rt)),
            ],
        ),
        Store {
            index: i,
            message: text,
        } => object_for(
            rt,
            vec![
                ("phase", string("store")),
                ("index", index(*i)),
                ("message", string(text)),
            ],
        ),
    }
}
fn branch(failure: &ByCasesBranchFailed, rt: &Runtime) -> JsonValue {
    use ByCasesBranchFailed::*;
    match failure {
        AssumeCase(text) => message("assume_case", text, rt),
        ProofBody(failure) => body(failure, rt),
        ClosingThen { then_index, result } => object_for(
            rt,
            vec![
                ("phase", string("closing_then")),
                ("then_index", index(*then_index)),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
        ClosingImpossible(failure) => object_for(
            rt,
            vec![
                ("phase", string("closing_impossible")),
                ("failure", closing(failure, rt)),
            ],
        ),
    }
}
fn closing(failure: &ByContradictionClosingFailed, rt: &Runtime) -> JsonValue {
    use ByContradictionClosingFailed::*;
    match failure {
        Impossible(result) => verify("impossible", result, rt),
        NegateImpossibleUnsupported(text) => message("negate_impossible", text, rt),
        NegatedImpossible(result) => verify("negated_impossible", result, rt),
    }
}
pub(in crate::json_output) fn project_contra_failure(
    failure: &ExecByContraStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecByContraStmtFailed::*;
    match failure {
        GoalWd(result) => wd(result, rt),
        NegationUnsupported(text) => message("negation_unsupported", text, rt),
        NegationAssume(text) => message("negation_assume", text, rt),
        ProofBody(failure) => body(failure, rt),
        Closing(failure) => object_for(
            rt,
            vec![
                ("phase", string("closing")),
                ("failure", closing(failure, rt)),
            ],
        ),
        Store(text) => message("store", text, rt),
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/json_output/proof_block_failure/tests.rs"]
mod proof_block_failure_tests;
