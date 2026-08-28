//! Tuple and Cartesian-product property facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct IsTupleFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsTupleFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsCartFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsCartFact {
    pub set: Obj,
    pub line_file: LineFile,
}

impl IsCartFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsCartFact { set, line_file }
    }
}

impl NotIsCartFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsCartFact { set, line_file }
    }
}

impl IsTupleFact {
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        IsTupleFact {
            set: tuple,
            line_file,
        }
    }
}

impl NotIsTupleFact {
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        NotIsTupleFact {
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
