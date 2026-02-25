use std::fmt;

/// 算术相关错误（如非算术表达式、除零等）
#[derive(Debug)]
pub struct ArithmeticError{
    pub msg: String,
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for ArithmeticError {}

impl ArithmeticError {
    pub fn new(msg: &str) -> Self {
        ArithmeticError { msg: msg.to_string() }
    }
}
