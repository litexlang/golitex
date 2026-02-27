use std::fmt;

#[derive(Debug)]
pub enum Err {
    ArithmeticErr(ArithmeticErr),
}

/// 算术相关错误（如非算术表达式、除零等）
#[derive(Debug)]
pub struct ArithmeticErr{
    pub msg: String,
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::ArithmeticErr(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for Err {}

impl fmt::Display for ArithmeticErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for ArithmeticErr {}

impl ArithmeticErr {
    pub fn new(msg: &str) -> Self {
        ArithmeticErr { msg: msg.to_string() }
    }
}
