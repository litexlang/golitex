//! Subset and superset fact payloads.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct SupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct SubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl SubsetFact {
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SubsetFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl NotSubsetFact {
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSubsetFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl SupersetFact {
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SupersetFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl NotSupersetFact {
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSupersetFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl fmt::Display for SupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{} {}",
            self.left, FACT_PREFIX, SUPERSET, self.right
        )
    }
}

impl fmt::Display for NotSupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.left, FACT_PREFIX, SUPERSET, self.right
        )
    }
}

impl fmt::Display for SubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{} {}", self.left, FACT_PREFIX, SUBSET, self.right)
    }
}

impl fmt::Display for NotSubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.left, FACT_PREFIX, SUBSET, self.right
        )
    }
}
