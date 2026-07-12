use crate::common::json_value::JsonValue;
use crate::prelude::{ExecutionPhaseTrace, StatementExecutionTrace, StatementPhaseStatus};

pub(crate) fn execution_phases_value(
    trace: &StatementExecutionTrace,
    well_definedness_checks: Vec<JsonValue>,
    process_fields: Vec<(String, JsonValue)>,
    environment_effects: Vec<JsonValue>,
) -> JsonValue {
    JsonValue::Object(vec![
        (
            "verify_well_definedness".to_string(),
            phase_value(
                &trace.verify_well_definedness,
                vec![(
                    "checks".to_string(),
                    JsonValue::Array(well_definedness_checks),
                )],
            ),
        ),
        (
            "verify_process".to_string(),
            phase_value(&trace.verify_process, process_fields),
        ),
        (
            "affect_environment".to_string(),
            phase_value(
                &trace.affect_environment,
                vec![("effects".to_string(), JsonValue::Array(environment_effects))],
            ),
        ),
    ])
}

pub(crate) fn error_execution_phases_value(trace: &StatementExecutionTrace) -> JsonValue {
    execution_phases_value(trace, vec![], vec![], vec![])
}

fn phase_value(trace: &ExecutionPhaseTrace, mut fields: Vec<(String, JsonValue)>) -> JsonValue {
    let mut output = vec![(
        "status".to_string(),
        JsonValue::JsonString(phase_status_text(trace.status).to_string()),
    )];
    if let Some(message) = trace.message.as_ref() {
        output.push((
            "message".to_string(),
            JsonValue::JsonString(message.clone()),
        ));
    }
    output.append(&mut fields);
    JsonValue::Object(output)
}

fn phase_status_text(status: StatementPhaseStatus) -> &'static str {
    match status {
        StatementPhaseStatus::Success => "success",
        StatementPhaseStatus::Unknown => "unknown",
        StatementPhaseStatus::Error => "error",
        StatementPhaseStatus::Skipped => "skipped",
        StatementPhaseStatus::NotRun => "not_run",
    }
}
