//! Set, nonempty-set, and finite-set property facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct IsSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsNonemptySetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsNonemptySetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsFiniteSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsFiniteSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

impl IsSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsSetFact { set, line_file }
    }
}

impl NotIsSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsSetFact { set, line_file }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsNonemptySetFact { set, line_file }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsNonemptySetFact { set, line_file }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsFiniteSetFact { set, line_file }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsFiniteSetFact { set, line_file }
    }
}

impl fmt::Display for IsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}", FACT_PREFIX, IS_SET, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            IS_NONEMPTY_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for NotIsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_NONEMPTY_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            IS_FINITE_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for NotIsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_FINITE_SET,
            braced_string(&self.set)
        )
    }
}
