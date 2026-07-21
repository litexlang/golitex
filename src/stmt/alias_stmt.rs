use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct AliasPropStmt {
    pub new_name: String,
    pub target_name: AtomicName,
    pub line_file: LineFile,
}

impl AliasPropStmt {
    pub fn new(new_name: String, target_name: AtomicName, line_file: LineFile) -> Self {
        AliasPropStmt {
            new_name,
            target_name,
            line_file,
        }
    }
}

impl fmt::Display for AliasPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {} {} {}",
            ALIAS, PROP, self.new_name, EQUIVALENT_SIGN, self.target_name
        )
    }
}

#[derive(Clone)]
pub struct AliasThmStmt {
    pub new_name: String,
    pub target_name: AtomicName,
    pub line_file: LineFile,
}

impl AliasThmStmt {
    pub fn new(new_name: String, target_name: AtomicName, line_file: LineFile) -> Self {
        AliasThmStmt {
            new_name,
            target_name,
            line_file,
        }
    }
}

impl fmt::Display for AliasThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {} {} {}",
            ALIAS, THM, self.new_name, EQUIVALENT_SIGN, self.target_name
        )
    }
}
