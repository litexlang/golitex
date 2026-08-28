//! Standard error and display integration.

use super::{RuntimeError, RuntimeErrorStruct};
use std::fmt;

impl std::error::Error for RuntimeError {}

// Display outputs a short placeholder; JSON: `display_runtime_error_json` in `crate::pipeline`.
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", "error")
    }
}

impl fmt::Display for RuntimeErrorStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for RuntimeErrorStruct {}
