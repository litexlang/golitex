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

impl Stmt {
    pub fn line(&self) -> u32 {
        match self {
            Stmt::Fact(fact) => fact.line(),
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            Stmt::Fact(fact) => fact.file_index(),
        }
    }

    pub fn str_with_line_file(&self) -> String {
        match self {
            Stmt::Fact(fact) => fact.str_with_line_file(),
        }
    }
}