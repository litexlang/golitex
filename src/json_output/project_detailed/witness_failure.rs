use super::verify::project_verify_fact;
use super::wd::{project_param_type_wd, project_verify_obj_wd};
use crate::execute::execute_witness_stmt::{
    ExecWitnessAtomicFactStmtFailed, ExecWitnessExistFactStmtFailed,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_witness_atomic_failure(
    failure: &ExecWitnessAtomicFactStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecWitnessAtomicFactStmtFailed::*;
    match failure {
        AbstractProp => phase("abstract_prop", rt),
        PropNotFound => phase("prop_not_found", rt),
        BadDefinition(message) => message_phase("definition", message, rt),
        Instantiate(message) => message_phase("instantiate", message, rt),
        PropArgumentType { index, result } => object_for(
            rt,
            vec![
                ("phase", string("prop_argument_type")),
                ("index", JsonValue::Number(*index as f64)),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
        ExistCheck(failure) => object_for(
            rt,
            vec![
                ("phase", string("exist_check")),
                ("failure", project_witness_exist_failure(failure, rt)),
            ],
        ),
    }
}

pub(super) fn project_witness_exist_failure(
    failure: &ExecWitnessExistFactStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecWitnessExistFactStmtFailed::*;
    match failure {
        WitnessCountMismatch => phase("witness_count", rt),
        ExistFactWellDefined(failure) => object_for(
            rt,
            vec![
                ("phase", string("exist_well_defined")),
                (
                    "failure",
                    super::wd_failure::project_fact_wd_failure(failure, rt),
                ),
            ],
        ),
        WitnessObjWellDefined(result) => object_for(
            rt,
            vec![
                ("phase", string("witness_well_defined")),
                ("result", project_verify_obj_wd(result, rt)),
            ],
        ),
        WitnessTypeInstantiate(message) => message_phase("witness_type_instantiate", message, rt),
        WitnessType(result) => verify_phase("witness_type", result, rt),
        IntroduceBinders(failure) => object_for(
            rt,
            vec![
                ("phase", string("introduce_binders")),
                ("failure", project_introduce_failure(failure, rt)),
            ],
        ),
        ProofBody(failure) => object_for(
            rt,
            vec![
                ("phase", string("proof_body")),
                ("step_index", JsonValue::Number(failure.step_index as f64)),
                (
                    "result",
                    super::stmt::project_stmt_detailed(&failure.result, rt),
                ),
            ],
        ),
        BodyCheck(result) => verify_phase("body_check", result, rt),
        BodyInstantiate => phase("body_instantiate", rt),
        Uniqueness(result) => verify_phase("uniqueness", result, rt),
    }
}

fn project_introduce_failure(
    failure: &crate::execute::IntroduceTypedParametersFailed,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::IntroduceTypedParametersFailed::*;
    match failure {
        ParamType(result) => object_for(
            rt,
            vec![
                ("phase", string("param_type")),
                ("result", project_verify_obj_wd(result, rt)),
            ],
        ),
        AutoOpenStructLayer {
            param_type_well_defined,
            defined_params,
            opened_before_fail,
            failed,
        } => object_for(
            rt,
            vec![
                ("phase", string("auto_open_struct_layer")),
                (
                    "param_type_well_defined",
                    JsonValue::Array(
                        param_type_well_defined
                            .iter()
                            .map(|p| project_param_type_wd(p, rt))
                            .collect(),
                    ),
                ),
                (
                    "defined_params",
                    super::store::project_have_store_ids(&defined_params.stored_fact_ids, rt),
                ),
                (
                    "opened_before_fail",
                    JsonValue::Array(
                        opened_before_fail
                            .iter()
                            .map(|p| {
                                object_for(
                                    rt,
                                    vec![
                                        ("obj", string(p.obj.readable_string())),
                                        ("struct_obj", string(p.struct_obj.readable_string())),
                                        (
                                            "store_and_infer",
                                            JsonValue::Array(
                                                p.store_and_infer
                                                    .iter()
                                                    .map(|p| {
                                                        super::store::project_store_and_infer(p, rt)
                                                    })
                                                    .collect(),
                                            ),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
                (
                    "failure",
                    object_for(
                        rt,
                        vec![
                            ("obj", string(failed.obj.readable_string())),
                            ("struct_obj", string(failed.struct_obj.readable_string())),
                            ("reason", string(&failed.reason)),
                        ],
                    ),
                ),
            ],
        ),
    }
}

fn phase(name: &str, rt: &Runtime) -> JsonValue {
    object_for(rt, vec![("phase", string(name))])
}

fn message_phase(name: &str, message: &str, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![("phase", string(name)), ("message", string(message))],
    )
}

fn verify_phase(
    name: &str,
    result: &crate::execute::execute_fact_stmt::VerifyFactResult,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", string(name)),
            ("result", project_verify_fact(result, rt)),
        ],
    )
}

#[cfg(test)]
#[path = "../../../tests/unit/json_output/witness_failure/tests.rs"]
mod tests;
