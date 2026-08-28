//! Positive and negative membership facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct InFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotInFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

impl InFact {
    pub fn new(element: Obj, set: Obj, line_file: LineFile) -> Self {
        InFact {
            element,
            set,
            line_file,
        }
    }
}

impl NotInFact {
    pub fn new(element: Obj, set: Obj, line_file: LineFile) -> Self {
        NotInFact {
            element,
            set,
            line_file,
        }
    }
}

impl fmt::Display for InFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{} {}", self.element, FACT_PREFIX, IN, self.set)
    }
}

impl fmt::Display for NotInFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.element, FACT_PREFIX, IN, self.set
        )
    }
}
