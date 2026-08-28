//! Function ranges and predicate-defined replacements.

use crate::prelude::*;

#[derive(Clone)]
pub struct FnRange {
    pub function: Box<Obj>,
}

#[derive(Clone)]
pub struct Replacement {
    pub prop_name: AtomicName,
    pub source_set: Box<Obj>,
}

impl FnRange {
    pub fn new(function: Obj) -> Self {
        FnRange {
            function: Box::new(function),
        }
    }
}

impl Replacement {
    pub fn new(prop_name: AtomicName, source_set: Obj) -> Self {
        Replacement {
            prop_name,
            source_set: Box::new(source_set),
        }
    }
}
