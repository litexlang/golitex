use crate::runtime::CodeSource;

// Source location on AST: line plus source path and publication identity.
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
