//! Subset and superset fact payloads.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct SupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct SubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl SubsetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SubsetFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotSubsetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSubsetFact {
            left,
            right,
            line_file,
        }
    }
}

impl SupersetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SupersetFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotSupersetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSupersetFact {
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
