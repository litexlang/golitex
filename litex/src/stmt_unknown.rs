use std::fmt;
use crate::keywords::UNKNOWN;

pub struct StmtUnknown {
}

impl fmt::Display for StmtUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", UNKNOWN)
    }
}

impl StmtUnknown {
    pub fn new() -> Self {
        StmtUnknown { }
    }
}
