use crate::fact::Fact;
use std::fmt;
use crate::consts::UNKNOWN;
use crate::helper::on_line_in_file_colon;

pub struct StmtUnknown<'a> {
    pub fact: &'a Fact,
}

impl<'a> fmt::Display for StmtUnknown<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (line, file_index) = self.fact.line_file();
        write!(f, "{} {}\n{}", UNKNOWN, on_line_in_file_colon(line, file_index), self.fact)
    }
}

impl<'a> StmtUnknown<'a> {
    pub fn new(fact: &'a Fact) -> Self {
        StmtUnknown { fact }
    }
}