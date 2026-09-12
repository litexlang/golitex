use crate::new_pipeline::runtime::RealOrVirtualPath;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSpan {
    pub line: usize,
    pub path: RealOrVirtualPath,
}

impl SourceSpan {
    pub fn new(line: usize, path: RealOrVirtualPath) -> Self {
        Self { line, path }
    }
}
