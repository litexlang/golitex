//! Tuple and Cartesian-product property facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct IsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsCartFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsCartFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: LineFile,
}

impl IsCartFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsCartFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl NotIsCartFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsCartFact {
            fact_id: FactId::fresh(),
            set,
            line_file,
        }
    }
}

impl IsTupleFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        IsTupleFact {
            fact_id: FactId::fresh(),
            set: tuple,
            line_file,
        }
    }
}

impl NotIsTupleFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        NotIsTupleFact {
            fact_id: FactId::fresh(),
            set: tuple,
            line_file,
        }
    }
}

impl fmt::Display for IsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}", FACT_PREFIX, IS_CART, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_CART,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}", FACT_PREFIX, IS_TUPLE, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_TUPLE,
            braced_string(&self.set)
        )
    }
}
