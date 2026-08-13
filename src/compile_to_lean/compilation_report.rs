use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanCompilationStatus {
    Complete,
    Incomplete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanCompilationPhase {
    IrConstruction,
    LeanEmission,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexToLeanUnsupportedStatement {
    pub statement_index: usize,
    pub statement: String,
    pub line: usize,
    pub source_path: String,
    pub phase: LitexToLeanCompilationPhase,
    pub reason: String,
}

impl LitexToLeanUnsupportedStatement {
    pub(crate) fn new(
        statement_index: usize,
        statement: String,
        line_file: &LineFile,
        phase: LitexToLeanCompilationPhase,
        reason: String,
    ) -> Self {
        LitexToLeanUnsupportedStatement {
            statement_index,
            statement,
            line: line_file.0,
            source_path: line_file.1.to_string(),
            phase,
            reason,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexToLeanCompilationReport {
    pub lean_code: String,
    pub status: LitexToLeanCompilationStatus,
    pub unsupported: Vec<LitexToLeanUnsupportedStatement>,
}

impl LitexToLeanCompilationReport {
    pub(crate) fn new(
        lean_code: String,
        unsupported: Vec<LitexToLeanUnsupportedStatement>,
    ) -> Self {
        let status = if unsupported.is_empty() {
            LitexToLeanCompilationStatus::Complete
        } else {
            LitexToLeanCompilationStatus::Incomplete
        };
        LitexToLeanCompilationReport {
            lean_code,
            status,
            unsupported,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.status == LitexToLeanCompilationStatus::Complete
    }
}
