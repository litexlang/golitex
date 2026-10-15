use crate::prelude::*;

pub(in crate::json_output) fn project_by_def_failure(
    failure: &ExecByDefStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecByDefStmtFailed::Definition(failed) => project_definition_failure(failed, rt),
        ExecByDefStmtFailed::GoalWd(result) => super::helper::failure_stage(
            rt,
            "goal_wd",
            super::super::failure_kind::FailureKind::WellDefined,
            "result",
            super::wd::project_verify_fact_wd_result(result, rt),
        ),
        ExecByDefStmtFailed::Proof(result) => super::helper::verification_failure(
            rt,
            "proof",
            result,
            super::super::failure_kind::FailureKind::ProofSearch,
        ),
        ExecByDefStmtFailed::Store(message) => super::helper::failure_message(
            rt,
            "store",
            super::super::failure_kind::FailureKind::Storage,
            message,
        ),
    }
}

pub(in crate::json_output) fn project_by_for_failure(
    failure: &ExecByForStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecByForStmtFailed::ProofBody(failed) => super::proof_block_failure::body(failed, rt),
        ExecByForStmtFailed::GoalWd(result) => super::helper::failure_stage(
            rt,
            "goal_wd",
            super::super::failure_kind::FailureKind::WellDefined,
            "result",
            super::wd::project_verify_fact_wd_result(result, rt),
        ),
        ExecByForStmtFailed::Domain(message) => super::helper::failure_message(
            rt,
            "domain",
            super::super::failure_kind::FailureKind::Domain,
            message,
        ),
        ExecByForStmtFailed::Assignment {
            index,
            then_index,
            result,
        } => {
            let projected = super::super::helper::object_for(
                rt,
                vec![
                    ("phase", super::super::helper::string("assignment")),
                    ("index", JsonValue::Number(*index as f64)),
                    ("then_index", JsonValue::Number(*then_index as f64)),
                    ("result", super::verify::project_verify_fact(result, rt)),
                ],
            );
            super::super::helper::inherit_failure_field(rt, projected, "result")
        }
        ExecByForStmtFailed::Instantiate(message) => super::helper::failure_message(
            rt,
            "instantiate",
            super::super::failure_kind::FailureKind::Instantiation,
            message,
        ),
        ExecByForStmtFailed::Store(message) => super::helper::failure_message(
            rt,
            "store",
            super::super::failure_kind::FailureKind::Storage,
            message,
        ),
    }
}

pub(in crate::json_output) fn project_enumerate_failure(
    failure: &ExecByEnumerateFiniteSetStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecByEnumerateFiniteSetStmtFailed::ProofBody(failed) => {
            super::proof_block_failure::body(failed, rt)
        }
        ExecByEnumerateFiniteSetStmtFailed::GoalWd(result) => super::helper::failure_stage(
            rt,
            "goal_wd",
            super::super::failure_kind::FailureKind::WellDefined,
            "result",
            super::wd::project_verify_fact_wd_result(result, rt),
        ),
        ExecByEnumerateFiniteSetStmtFailed::Domain(message) => super::helper::failure_message(
            rt,
            "domain",
            super::super::failure_kind::FailureKind::Domain,
            message,
        ),
        ExecByEnumerateFiniteSetStmtFailed::Assignment {
            index,
            then_index,
            result,
        } => {
            let projected = super::super::helper::object_for(
                rt,
                vec![
                    ("phase", super::super::helper::string("assignment")),
                    ("index", JsonValue::Number(*index as f64)),
                    ("then_index", JsonValue::Number(*then_index as f64)),
                    ("result", super::verify::project_verify_fact(result, rt)),
                ],
            );
            super::super::helper::inherit_failure_field(rt, projected, "result")
        }
        ExecByEnumerateFiniteSetStmtFailed::Instantiate(message) => super::helper::failure_message(
            rt,
            "instantiate",
            super::super::failure_kind::FailureKind::Instantiation,
            message,
        ),
        ExecByEnumerateFiniteSetStmtFailed::Store(message) => super::helper::failure_message(
            rt,
            "store",
            super::super::failure_kind::FailureKind::Storage,
            message,
        ),
    }
}

fn project_definition_failure(failure: &DefinitionProofFailed, rt: &Runtime) -> JsonValue {
    use crate::json_output::failure_kind::FailureKind;
    use crate::json_output::helper::{
        inherit_failure_field, object_for, string, with_failure_diagnostic,
    };
    match failure {
        DefinitionProofFailed::Unavailable => super::helper::failure_message(
            rt,
            "definition_proof",
            FailureKind::DefinitionProofUnavailable,
            "no supported definition is available for this goal",
        ),
        DefinitionProofFailed::Arity { expected, actual } => with_failure_diagnostic(
            rt,
            object_for(
                rt,
                vec![
                    ("phase", string("arity")),
                    ("expected", JsonValue::Number(*expected as f64)),
                    ("actual", JsonValue::Number(*actual as f64)),
                ],
            ),
            FailureKind::Arity,
            vec![],
        ),
        DefinitionProofFailed::Instantiate(message) => {
            super::helper::failure_message(rt, "instantiate", FailureKind::Instantiation, message)
        }
        DefinitionProofFailed::Requirement {
            index,
            fact,
            result,
        } => {
            let value = object_for(
                rt,
                vec![
                    ("phase", string("definition_requirement")),
                    ("index", JsonValue::Number(*index as f64)),
                    ("goal", string(fact.readable_string())),
                    ("result", super::verify::project_verify_fact(result, rt)),
                ],
            );
            inherit_failure_field(rt, value, "result")
        }
    }
}
