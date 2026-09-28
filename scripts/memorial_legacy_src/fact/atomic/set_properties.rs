//! Set, nonempty-set, and finite-set property facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct IsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

impl IsSetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsSetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl NotIsSetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsSetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl IsNonemptySetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsNonemptySetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl NotIsNonemptySetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsNonemptySetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl IsFiniteSetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsFiniteSetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl NotIsFiniteSetFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsFiniteSetFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
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
