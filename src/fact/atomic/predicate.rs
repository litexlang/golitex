//! User predicate fact payloads.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct NormalAtomicFact {
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotNormalAtomicFact {
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: LineFile,
}

impl NormalAtomicFact {
    pub fn new(predicate: AtomicName, body: Vec<Obj>, line_file: LineFile) -> Self {
        NormalAtomicFact {
            predicate,
            body,
            line_file,
        }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: AtomicName, body: Vec<Obj>, line_file: LineFile) -> Self {
        NotNormalAtomicFact {
            predicate,
            body,
            line_file,
        }
    }
}

impl fmt::Display for NormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if let AtomicName::WithoutMod(name) = &self.predicate {
            if self.body.len() == 2 && matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET) {
                return write!(
                    f,
                    "{} {}{} {}",
                    self.body[0], FACT_PREFIX, name, self.body[1]
                );
            }
        }
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            self.predicate,
            braced_vec_to_string(&self.body)
        )
    }
}

impl fmt::Display for NotNormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if let AtomicName::WithoutMod(name) = &self.predicate {
            if self.body.len() == 2 && matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET) {
                return write!(
                    f,
                    "{} {} {}{} {}",
                    NOT, self.body[0], FACT_PREFIX, name, self.body[1]
                );
            }
        }
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            self.predicate,
            braced_vec_to_string(&self.body)
        )
    }
}
