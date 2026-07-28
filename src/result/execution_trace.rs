use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementPhaseStatus {
    Success,
    Unknown,
    Error,
    Skipped,
    NotRun,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementExecutionPhase {
    VerifyWellDefinedness,
    VerifyProcess,
    AffectEnvironment,
}

#[derive(Clone, Debug)]
pub struct ExecutionPhaseTrace {
    pub status: StatementPhaseStatus,
    pub message: Option<String>,
}

impl ExecutionPhaseTrace {
    pub fn new(status: StatementPhaseStatus, message: Option<String>) -> Self {
        ExecutionPhaseTrace { status, message }
    }
}

#[derive(Clone, Debug)]
pub struct StatementExecutionTrace {
    pub verify_well_definedness: ExecutionPhaseTrace,
    pub verify_process: ExecutionPhaseTrace,
    pub affect_environment: ExecutionPhaseTrace,
    pub verification_status: Option<String>,
    pub trust_summary: ProofTrustSummary,
}

impl StatementExecutionTrace {
    pub fn verified(process_is_unknown: bool) -> Self {
        let process_status = if process_is_unknown {
            StatementPhaseStatus::Unknown
        } else {
            StatementPhaseStatus::Success
        };
        StatementExecutionTrace {
            verify_well_definedness: ExecutionPhaseTrace::new(StatementPhaseStatus::Success, None),
            verify_process: ExecutionPhaseTrace::new(process_status, None),
            affect_environment: ExecutionPhaseTrace::new(StatementPhaseStatus::Success, None),
            verification_status: None,
            trust_summary: ProofTrustSummary::new(),
        }
    }

    pub fn trusted() -> Self {
        StatementExecutionTrace {
            verify_well_definedness: ExecutionPhaseTrace::new(
                StatementPhaseStatus::Skipped,
                Some("trusted file load".to_string()),
            ),
            verify_process: ExecutionPhaseTrace::new(
                StatementPhaseStatus::Skipped,
                Some("trusted file load".to_string()),
            ),
            affect_environment: ExecutionPhaseTrace::new(StatementPhaseStatus::Success, None),
            verification_status: None,
            trust_summary: ProofTrustSummary::new(),
        }
    }

    pub fn trusted_prefix(trust_summary: ProofTrustSummary) -> Self {
        Self::trusted().with_trusted_prefix(trust_summary)
    }

    pub fn with_trusted_prefix(mut self, trust_summary: ProofTrustSummary) -> Self {
        let message = Some("trusted_prefix".to_string());
        self.verify_well_definedness =
            ExecutionPhaseTrace::new(StatementPhaseStatus::Skipped, message.clone());
        self.verify_process = ExecutionPhaseTrace::new(StatementPhaseStatus::Skipped, message);
        self.verification_status = Some("trusted_prefix".to_string());
        self.trust_summary = trust_summary;
        self
    }

    pub fn with_verified_status(mut self) -> Self {
        self.verification_status = Some("verified".to_string());
        self.trust_summary = ProofTrustSummary::new();
        self
    }

    pub fn with_indirect_trust(mut self, trust_summary: ProofTrustSummary) -> Self {
        self.verification_status = Some("indirect_trust".to_string());
        self.trust_summary = trust_summary;
        self
    }

    pub fn unknown() -> Self {
        StatementExecutionTrace {
            verify_well_definedness: ExecutionPhaseTrace::new(StatementPhaseStatus::Success, None),
            verify_process: ExecutionPhaseTrace::new(StatementPhaseStatus::Unknown, None),
            affect_environment: ExecutionPhaseTrace::new(
                StatementPhaseStatus::NotRun,
                Some("verification is unknown".to_string()),
            ),
            verification_status: None,
            trust_summary: ProofTrustSummary::new(),
        }
    }

    pub fn failed(phase: StatementExecutionPhase, message: String) -> Self {
        let success = ExecutionPhaseTrace::new(StatementPhaseStatus::Success, None);
        let error = ExecutionPhaseTrace::new(StatementPhaseStatus::Error, Some(message));
        let not_run = ExecutionPhaseTrace::new(
            StatementPhaseStatus::NotRun,
            Some("previous phase failed".to_string()),
        );
        match phase {
            StatementExecutionPhase::VerifyWellDefinedness => StatementExecutionTrace {
                verify_well_definedness: error,
                verify_process: not_run.clone(),
                affect_environment: not_run,
                verification_status: None,
                trust_summary: ProofTrustSummary::new(),
            },
            StatementExecutionPhase::VerifyProcess => StatementExecutionTrace {
                verify_well_definedness: success,
                verify_process: error,
                affect_environment: not_run,
                verification_status: None,
                trust_summary: ProofTrustSummary::new(),
            },
            StatementExecutionPhase::AffectEnvironment => StatementExecutionTrace {
                verify_well_definedness: success.clone(),
                verify_process: success,
                affect_environment: error,
                verification_status: None,
                trust_summary: ProofTrustSummary::new(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trust_before_line_trace_uses_distinct_status_and_phase_message() {
        let summary = ProofTrustSummary::cli_trusted_prefix(default_line_file(), 42);
        let trace = StatementExecutionTrace::trusted_prefix(summary);

        assert_eq!(trace.verification_status.as_deref(), Some("trusted_prefix"));
        assert_eq!(
            trace.verify_process.message.as_deref(),
            Some("trusted_prefix")
        );
        assert_eq!(trace.trust_summary.dependencies[0].boundary, Some(42));
    }

    #[test]
    fn ordinary_trusted_trace_keeps_existing_message_without_output_status() {
        let trace = StatementExecutionTrace::trusted();

        assert_eq!(trace.verification_status, None);
        assert_eq!(
            trace.verify_process.message.as_deref(),
            Some("trusted file load")
        );
        assert!(trace.trust_summary.is_empty());
    }
}
