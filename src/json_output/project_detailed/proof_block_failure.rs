//! Mirror the existing failed proof stages without changing execution.
use super::verify::project_verify_fact;
use super::wd::project_verify_fact_wd_result;
use crate::execute::execute_by_stmt::{
    ByCasesBranchFailed, ByCasesEnteredBranchFailed, ByContradictionClosingFailed,
    ExecByCasesStmtFailed, ExecByContraStmtFailed, ExecByExtensionStmtFailed,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyFailed, ExecClaimForallEnteredFailed, ExecClaimForallFailed,
    ExecClaimNonForallFailed, ExecClaimStmtFailed, ExecSketchStmtFailed, ProofBlockBodyFailed,
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
    let projected = {
        object_for(
            rt,
            vec![
                ("phase", string(phase)),
                ("result", project_verify_fact(result, rt)),
            ],
        )
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}
fn wd(
    result: &crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
        object_for(
            rt,
            vec![
                ("phase", string("goal_wd")),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        )
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}
fn index(value: usize) -> JsonValue {
    JsonValue::Number(value as f64)
}
pub(in crate::json_output) fn body(failure: &ProofBlockBodyFailed, rt: &Runtime) -> JsonValue {
    let projected = {
        object_for(
            rt,
            vec![
                ("phase", string("proof_body")),
                ("step_index", index(failure.step_index)),
                ("statement", string(failure.statement.readable_string())),
                (
                    "source_location",
                    crate::json_output::source::project_statement_source(&failure.statement, rt),
                ),
                (
                    "result",
                    super::stmt::project_stmt_detailed(&failure.result, rt),
                ),
            ],
        )
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}

pub(in crate::json_output) fn project_claim_failure(
    failure: &ExecClaimStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
        use ExecClaimStmtFailed::*;
        match failure {
            GoalWd(result) => wd(result, rt),
            GoalUnsupported(text) => message("goal_unsupported", text, rt),
            Local(context) => project_claim_body_failure(&context.body, rt),
            Store { message: text, .. } => message("store", text, rt),
        }
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}

fn project_claim_body_failure(failure: &ExecClaimBodyFailed, rt: &Runtime) -> JsonValue {
    match failure {
        ExecClaimBodyFailed::NonForall(failed) => match failed {
            ExecClaimNonForallFailed::ProofBody(failed) => body(failed, rt),
            ExecClaimNonForallFailed::Conclusion { result, .. } => {
                project_claim_conclusion_failure(0, result, rt)
            }
        },
        ExecClaimBodyFailed::Forall(failed) => match failed {
            ExecClaimForallFailed::Introduce(_) => message(
                "introduce",
                "claim: failed to introduce forall parameters",
                rt,
            ),
            ExecClaimForallFailed::Entered { failure, .. } => match failure {
                ExecClaimForallEnteredFailed::PremiseWd { .. } => message(
                    "introduce",
                    "claim: forall domain fact is not well-defined",
                    rt,
                ),
                ExecClaimForallEnteredFailed::ProofBody(failed) => body(failed, rt),
                ExecClaimForallEnteredFailed::Conclusion { index, result, .. } => {
                    project_claim_conclusion_failure(*index, result, rt)
                }
            },
        },
    }
}

fn project_claim_conclusion_failure(
    failed_index: usize,
    result: &crate::execute::execute_fact_stmt::VerifyFactResult,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", string("conclusion")),
            ("index", index(failed_index)),
            ("result", project_verify_fact(result, rt)),
        ],
    )
}

pub(in crate::json_output) fn project_sketch_failure(
    failure: &ExecSketchStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
        match failure {
            ExecSketchStmtFailed::ProofBody(failure) => body(failure, rt),
        }
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}

pub(in crate::json_output) fn project_extension_failure(
    failure: &ExecByExtensionStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
        use ExecByExtensionStmtFailed::*;
        match failure {
            GoalWd(result) => wd(result, rt),
            ProofBody(failure) => body(failure, rt),
            LeftToRight(result) => verify("left_to_right", result, rt),
            RightToLeft(result) => verify("right_to_left", result, rt),
            Store(text) => message("store", text, rt),
        }
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}

pub(in crate::json_output) fn project_cases_failure(
    failure: &ExecByCasesStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
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
            Branch {
                index: i, failed, ..
            } => object_for(
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
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}
fn branch(failure: &ByCasesBranchFailed, rt: &Runtime) -> JsonValue {
    match failure {
        ByCasesBranchFailed::AssumeCase(text) => message("assume_case", text, rt),
        ByCasesBranchFailed::AfterAssumption(context) => entered_branch(&context.failure, rt),
    }
}
fn entered_branch(failure: &ByCasesEnteredBranchFailed, rt: &Runtime) -> JsonValue {
    let projected = {
        use ByCasesEnteredBranchFailed::*;
        match failure {
            ProofBody(failure) => body(failure, rt),
            ClosingThen {
                then_index, result, ..
            } => object_for(
                rt,
                vec![
                    ("phase", string("closing_then")),
                    ("then_index", index(*then_index)),
                    ("result", project_verify_fact(result, rt)),
                ],
            ),
            ClosingImpossible { failed, .. } => object_for(
                rt,
                vec![
                    ("phase", string("closing_impossible")),
                    ("failure", closing(failed, rt)),
                ],
            ),
        }
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}
fn closing(failure: &ByContradictionClosingFailed, rt: &Runtime) -> JsonValue {
    let projected = {
        use ByContradictionClosingFailed::*;
        match failure {
            AfterImpossible(context) => {
                let mut value = match &context.failure {
                    crate::execute::execute_by_stmt::ByContradictionOppositeFailed::NegationUnsupported(text) => message("negate_impossible", text, rt),
                    crate::execute::execute_by_stmt::ByContradictionOppositeFailed::Verification(result) => verify("negated_impossible", result, rt),
                };
                if let JsonValue::Object(fields) = &mut value {
                    fields.insert(
                        "proved_impossible".into(),
                        project_verify_fact(&context.impossible, rt),
                    );
                }
                value
            }
            Impossible(result) => verify("impossible", result, rt),
            NegateImpossibleUnsupported(text) => message("negate_impossible", text, rt),
            NegatedImpossible(result) => verify("negated_impossible", result, rt),
        }
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}
pub(in crate::json_output) fn project_contra_failure(
    failure: &ExecByContraStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    let projected = {
        use ExecByContraStmtFailed::*;
        match failure {
            Negation(context) => message("negation_unsupported", &context.message, rt),
            Local(context) => match &context.failure {
                crate::execute::execute_by_stmt::ExecByContraEnteredFailed::AssumptionWd(
                    result,
                ) => {
                    let mut value =
                        message("negation_assume", "assumption well-definedness failed", rt);
                    if let JsonValue::Object(fields) = &mut value {
                        fields.insert(
                            "well_defined_result".into(),
                            super::wd::project_verify_fact_wd_result(result, rt),
                        );
                    }
                    value
                }
                crate::execute::execute_by_stmt::ExecByContraEnteredFailed::ProofBody {
                    failure,
                    ..
                } => body(failure, rt),
                crate::execute::execute_by_stmt::ExecByContraEnteredFailed::Closing {
                    failure,
                    ..
                } => object_for(
                    rt,
                    vec![
                        ("phase", string("closing")),
                        ("failure", closing(failure, rt)),
                    ],
                ),
            },
            StoreAfterProof(context) => {
                let mut value = message("store", "goal well-definedness failed at store", rt);
                if let JsonValue::Object(fields) = &mut value {
                    fields.insert(
                        "well_defined_result".into(),
                        super::wd::project_verify_fact_wd_result(&context.result, rt),
                    );
                }
                value
            }
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
    };
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "result");
    let projected = crate::json_output::helper::inherit_failure_field(rt, projected, "failure");
    projected
}

#[cfg(test)]
#[path = "../../../tests/unit/json_output/proof_block_failure/tests.rs"]
mod proof_block_failure_tests;
