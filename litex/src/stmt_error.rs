use std::fmt;
use crate::consts::ERROR_COLON;

#[derive(Debug)]
pub enum StmtError {
    ArithmeticError(ArithmeticError),
}

#[derive(Debug)]
pub struct ArithmeticError{
    pub msg: String,
}

impl std::error::Error for StmtError {}

impl fmt::Display for StmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtError::ArithmeticError(e) => write!(f, "{}\n{}", ERROR_COLON, e),
        }
    }
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl ArithmeticError {
    pub fn new(msg: &str) -> Self {
        ArithmeticError { msg: msg.to_string() }
    }
}
