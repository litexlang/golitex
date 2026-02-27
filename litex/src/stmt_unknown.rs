use crate::fact::Fact;
use std::fmt;
use crate::consts::UNKNOWN_COLON;

pub struct StmtUnknown<'a> {
    pub fact: &'a Fact,
}

impl<'a> fmt::Display for StmtUnknown<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", UNKNOWN_COLON, self.fact)
    }
}

impl<'a> StmtUnknown<'a> {
    pub fn new(fact: &'a Fact) -> Self {
        StmtUnknown { fact }
    }
}