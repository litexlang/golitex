#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompilationStatus {
    Complete,
    Incomplete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompilationPhase {
    IrConstruction,
    LeanEmission,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsupportedCompilationItem {
    pub statement_index: usize,
    pub statement: String,
    pub line: usize,
    pub source_path: String,
    pub phase: CompilationPhase,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilationReport {
    pub lean_code: String,
    pub status: CompilationStatus,
    pub unsupported: Vec<UnsupportedCompilationItem>,
}

impl CompilationReport {
    pub(crate) fn complete(lean_code: String) -> Self {
        Self {
            lean_code,
            status: CompilationStatus::Complete,
            unsupported: Vec::new(),
        }
    }

    pub(crate) fn incomplete_emission(source_label: &str, reason: String) -> Self {
        let compact_reason = reason.replace(['\n', '\r'], " ");
        Self {
            lean_code: format!(
                "-- Litex-to-Lean incomplete for {source_label}. DO NOT USE AS A PROOF ARTIFACT.\nimport Litex\n\n-- Lean emission: {compact_reason}\n"
            ),
            status: CompilationStatus::Incomplete,
            unsupported: vec![UnsupportedCompilationItem {
                statement_index: 1,
                statement: "native-carrier IR emission".into(),
                line: 0,
                source_path: source_label.into(),
                phase: CompilationPhase::LeanEmission,
                reason,
            }],
        }
    }

    pub fn is_complete(&self) -> bool {
        self.status == CompilationStatus::Complete
    }
}
