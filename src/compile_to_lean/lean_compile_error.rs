use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanCompileError {
    pub statement_index: Option<usize>,
    pub route: String,
    pub message: String,
}

impl LeanCompileError {
    pub fn new(route: &str, message: &str) -> Self {
        Self {
            statement_index: None,
            route: route.to_string(),
            message: message.to_string(),
        }
    }

    pub fn unsupported(route: &str) -> Self {
        Self::new(
            route,
            "This successful evidence route is not supported by the Lean MVP.",
        )
    }
}

impl fmt::Display for LeanCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.statement_index {
            Some(index) => write!(f, "statement {index}: {}: {}", self.route, self.message),
            None => write!(f, "{}: {}", self.route, self.message),
        }
    }
}

impl std::error::Error for LeanCompileError {}
