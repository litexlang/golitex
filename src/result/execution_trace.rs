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
        }
    }

    pub fn trusted_prefix() -> Self {
        Self::trusted().with_trusted_prefix()
    }

    pub fn with_trusted_prefix(mut self) -> Self {
        let message = Some("trusted_prefix".to_string());
        self.verify_well_definedness =
            ExecutionPhaseTrace::new(StatementPhaseStatus::Skipped, message.clone());
        self.verify_process = ExecutionPhaseTrace::new(StatementPhaseStatus::Skipped, message);
        self.verification_status = Some("trusted_prefix".to_string());
        self
    }

    pub fn with_verified_status(mut self) -> Self {
        self.verification_status = Some("verified".to_string());
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
            },
            StatementExecutionPhase::VerifyProcess => StatementExecutionTrace {
                verify_well_definedness: success,
                verify_process: error,
                affect_environment: not_run,
                verification_status: None,
            },
            StatementExecutionPhase::AffectEnvironment => StatementExecutionTrace {
                verify_well_definedness: success.clone(),
                verify_process: success,
                affect_environment: error,
                verification_status: None,
            },
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/result/execution_trace/tests.rs"]
mod tests;
