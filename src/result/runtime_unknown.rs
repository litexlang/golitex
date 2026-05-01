use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct StmtUnknown {
    pub detail: Option<Vec<String>>,
}

impl fmt::Display for StmtUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", UNKNOWN_COLON)?;
        if let Some(detail_lines) = &self.detail {
            if !detail_lines.is_empty() {
                write!(f, " {}", detail_lines.join("\n"))?;
            }
        }
        Ok(())
    }
}

impl StmtUnknown {
    pub fn new() -> Self {
        StmtUnknown { detail: None }
    }

    pub fn new_with_detail(detail: String) -> Self {
        Self::new_with_detail_lines(vec![detail])
    }

    pub fn new_with_detail_lines(detail_lines: Vec<String>) -> Self {
        if detail_lines.is_empty() {
            return StmtUnknown { detail: None };
        }
        StmtUnknown {
            detail: Some(detail_lines),
        }
    }

    pub fn detail_for_display(&self) -> String {
        self.detail
            .as_ref()
            .map(|lines| lines.join("\n"))
            .unwrap_or_default()
    }
}
