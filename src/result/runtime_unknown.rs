use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct StmtUnknown {
    pub detail: Option<String>,
}

impl fmt::Display for StmtUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", UNKNOWN_COLON)?;
        if let Some(detail) = &self.detail {
            write!(f, " {}", detail)?;
        }
        Ok(())
    }
}

impl StmtUnknown {
    pub fn new() -> Self {
        StmtUnknown { detail: None }
    }

    pub fn new_with_detail(detail: String) -> Self {
        StmtUnknown {
            detail: Some(detail),
        }
    }
}
