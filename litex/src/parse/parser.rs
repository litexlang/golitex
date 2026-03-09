use std::fmt;

pub struct Parser {
}

impl Parser {
    pub fn new() -> Self {
        Parser { }
    }
}

impl fmt::Display for Parser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Parser {{ }}")
    }
}