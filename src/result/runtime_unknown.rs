use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct StmtUnknown {}

impl fmt::Display for StmtUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", UNKNOWN_COLON)
    }
}

impl StmtUnknown {
    pub fn new() -> Self {
        StmtUnknown {}
    }
}
