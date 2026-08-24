use super::*;

#[test]
fn trust_before_line_trace_uses_distinct_status_and_phase_message() {
    let trace = StatementExecutionTrace::trusted_prefix();

    assert_eq!(trace.verification_status.as_deref(), Some("trusted_prefix"));
    assert_eq!(
        trace.verify_process.message.as_deref(),
        Some("trusted_prefix")
    );
}

#[test]
fn ordinary_trusted_trace_keeps_existing_message_without_output_status() {
    let trace = StatementExecutionTrace::trusted();

    assert_eq!(trace.verification_status, None);
    assert_eq!(
        trace.verify_process.message.as_deref(),
        Some("trusted file load")
    );
}
