use crate::new_pipeline::runtime::CodeSource;

// Source location on AST: line + live CodeSource (no absolute path).
// StandaloneFile / display paths live on Runtime.current_file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLine {
    pub line: usize,
    pub origin: CodeSource,
}

impl SourceLine {
    pub fn new(line: usize, origin: CodeSource) -> Self {
        Self { line, origin }
    }
}
