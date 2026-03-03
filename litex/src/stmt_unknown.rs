use crate::fact::Fact;
use std::fmt;
use crate::consts::UNKNOWN;
use crate::helper::line_file_suffix;

pub struct StmtUnknown<'a> {
    pub fact: &'a Fact,
}

impl<'a> fmt::Display for StmtUnknown<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let loc = line_file_suffix(self.fact.line_file());
        write!(f, "{}{}\n{}", UNKNOWN, loc, self.fact)
    }
}

impl<'a> StmtUnknown<'a> {
    pub fn new(fact: &'a Fact) -> Self {
        StmtUnknown { fact }
    }
}