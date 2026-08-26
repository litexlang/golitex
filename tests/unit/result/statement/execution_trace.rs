//! Statement execution-phase contracts.

use super::*;

#[test]
fn ordinary_trusted_trace_keeps_existing_message_without_output_status() {
    let trace = StatementExecutionTrace::trusted();

    assert_eq!(trace.verification_status, None);
    assert_eq!(
        trace.verify_process.message.as_deref(),
        Some("trusted file load")
    );
}
