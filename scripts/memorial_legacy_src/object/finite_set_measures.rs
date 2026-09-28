//! Finite-set size and extrema operations.

use crate::prelude::*;

#[derive(Clone)]
pub struct FiniteSetSize {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct FiniteSetMax {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct FiniteSetMin {
    pub set: Box<Obj>,
}

impl FiniteSetSize {
    pub fn new(set: Obj) -> Self {
        FiniteSetSize { set: Box::new(set) }
    }
}

impl FiniteSetMax {
    pub fn new(set: Obj) -> Self {
        FiniteSetMax { set: Box::new(set) }
    }
}

impl FiniteSetMin {
    pub fn new(set: Obj) -> Self {
        FiniteSetMin { set: Box::new(set) }
    }
}
