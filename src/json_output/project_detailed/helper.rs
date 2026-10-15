use crate::prelude::*;

pub(super) fn failure_stage(
    runtime: &Runtime,
    phase: &str,
    kind: super::super::failure_kind::FailureKind,
    field: &str,
    child: JsonValue,
) -> JsonValue {
    let projected = super::super::helper::object_for(
        runtime,
        vec![
            ("phase", super::super::helper::string(phase)),
            (field, child),
        ],
    );
    let projected = super::super::helper::inherit_failure_field(runtime, projected, field);
    super::super::helper::with_failure_diagnostic(runtime, projected, kind, vec![])
}

pub(super) fn failure_message(
    runtime: &Runtime,
    phase: &str,
    kind: super::super::failure_kind::FailureKind,
    message: &str,
) -> JsonValue {
    failure_stage(
        runtime,
        phase,
        kind,
        "message",
        super::super::helper::string(message),
    )
}

pub(super) fn verification_failure(
    runtime: &Runtime,
    phase: &str,
    result: &VerifyFactResult,
    purpose: super::super::failure_kind::FailureKind,
) -> JsonValue {
    failure_stage(
        runtime,
        phase,
        super::super::failure_kind::FailureKind::for_obligation(result, purpose),
        "result",
        super::verify::project_verify_fact(result, runtime),
    )
}

pub(super) fn obj_wd_failure(
    runtime: &Runtime,
    phase: &str,
    result: &VerifyObjWellDefinedResult,
) -> JsonValue {
    failure_stage(
        runtime,
        phase,
        super::super::failure_kind::FailureKind::WellDefined,
        "result",
        super::wd::project_verify_obj_wd(result, runtime),
    )
}

pub(super) fn fact_wd_failure(
    runtime: &Runtime,
    phase: &str,
    result: &FailToVerifyFactWellDefinedResult,
) -> JsonValue {
    failure_stage(
        runtime,
        phase,
        super::super::failure_kind::FailureKind::WellDefined,
        "failure",
        super::wd_failure::project_fact_wd_failure(result, runtime),
    )
}
