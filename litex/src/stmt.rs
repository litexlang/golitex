use std::fmt;
use crate::fact::Fact;

pub enum Stmt {
    Fact(Fact),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(fact) => write!(f, "{}", fact),
        }
    }
}