#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtResultToLeanCompilationStatus {
    Complete,
    Incomplete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtResultToLeanCompilationPhase {
    StmtResultReading,
    LeanSourceConstruction,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsupportedStmtResultToLeanCompilationItem {
    pub statement_index: usize,
    pub statement: String,
    pub line: usize,
    pub source_path: String,
    pub phase: StmtResultToLeanCompilationPhase,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StmtResultToLeanCompilationReport {
    pub lean_code: String,
    pub status: StmtResultToLeanCompilationStatus,
    pub unsupported: Vec<UnsupportedStmtResultToLeanCompilationItem>,
}

impl StmtResultToLeanCompilationReport {
    pub(crate) fn complete(lean_code: String) -> Self {
        Self {
            lean_code,
            status: StmtResultToLeanCompilationStatus::Complete,
            unsupported: Vec::new(),
        }
    }

    pub(crate) fn incomplete_lean_source_construction(source_label: &str, reason: String) -> Self {
        let compact_reason = reason.replace(['\n', '\r'], " ");
        Self {
            lean_code: format!(
                "-- Litex-to-Lean incomplete for {source_label}. DO NOT USE AS A PROOF ARTIFACT.\nimport Litex\n\n-- Lean emission: {compact_reason}\n"
            ),
            status: StmtResultToLeanCompilationStatus::Incomplete,
            unsupported: vec![UnsupportedStmtResultToLeanCompilationItem {
                statement_index: 1,
                statement: "native-carrier IR emission".into(),
                line: 0,
                source_path: source_label.into(),
                phase: StmtResultToLeanCompilationPhase::LeanSourceConstruction,
                reason,
            }],
        }
    }

    pub fn is_complete(&self) -> bool {
        self.status == StmtResultToLeanCompilationStatus::Complete
    }
}
