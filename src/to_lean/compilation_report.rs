use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToLeanCompilationStatus {
    Complete,
    Incomplete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToLeanUnsupportedPhase {
    IrConstruction,
    LeanEmission,
}

impl ToLeanUnsupportedPhase {
    pub(crate) fn label(self) -> &'static str {
        match self {
            ToLeanUnsupportedPhase::IrConstruction => "IR construction",
            ToLeanUnsupportedPhase::LeanEmission => "Lean emission",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToLeanUnsupported {
    pub statement_index: usize,
    pub statement: String,
    pub line: usize,
    pub source_path: String,
    pub phase: ToLeanUnsupportedPhase,
    pub reason: String,
}

impl ToLeanUnsupported {
    pub(crate) fn new(
        statement_index: usize,
        statement: String,
        line_file: &LineFile,
        phase: ToLeanUnsupportedPhase,
        reason: String,
    ) -> Self {
        ToLeanUnsupported {
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
pub struct ToLeanCompilationReport {
    pub lean_code: String,
    pub status: ToLeanCompilationStatus,
    pub unsupported: Vec<ToLeanUnsupported>,
}

impl ToLeanCompilationReport {
    pub(crate) fn new(lean_code: String, unsupported: Vec<ToLeanUnsupported>) -> Self {
        let status = if unsupported.is_empty() {
            ToLeanCompilationStatus::Complete
        } else {
            ToLeanCompilationStatus::Incomplete
        };
        ToLeanCompilationReport {
            lean_code,
            status,
            unsupported,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.status == ToLeanCompilationStatus::Complete
    }
}
