use std::fmt;
use crate::keywords::UNKNOWN;

pub struct StmtUnknown {
    pub fact: String,
    pub line_file_index: Option<(usize, usize)>,
}

impl fmt::Display for StmtUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((line, file_index)) = self.line_file_index {
            write!(f, "line {}, file index {}\n{}\n{}", line, file_index, UNKNOWN, self.fact)
        } else {
            write!(f, "{}\n{}", UNKNOWN, self.fact)
        }
    }
}

impl StmtUnknown {
    pub fn new(fact: String, line_file_index: Option<(usize, usize)>) -> Self {
        StmtUnknown { fact, line_file_index }
    }
}