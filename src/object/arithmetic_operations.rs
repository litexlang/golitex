//! Arithmetic operator objects.

use crate::prelude::*;

#[derive(Clone)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Quot {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Gcd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Lcm {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

impl Add {
    pub fn new(left: Obj, right: Obj) -> Self {
        Self::new_with_source_occurrence_id(left, right, None)
    }

    pub fn new_with_source_occurrence_id(
        left: Obj,
        right: Obj,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        Add {
            left: Box::new(left),
            right: Box::new(right),
            source_occurrence_id,
        }
    }
}

impl Sub {
    pub fn new(left: Obj, right: Obj) -> Self {
        Self::new_with_source_occurrence_id(left, right, None)
    }

    pub fn new_with_source_occurrence_id(
        left: Obj,
        right: Obj,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        Sub {
            left: Box::new(left),
            right: Box::new(right),
            source_occurrence_id,
        }
    }
}

impl Mul {
    pub fn new(left: Obj, right: Obj) -> Self {
        Self::new_with_source_occurrence_id(left, right, None)
    }

    pub fn new_with_source_occurrence_id(
        left: Obj,
        right: Obj,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        Mul {
            left: Box::new(left),
            right: Box::new(right),
            source_occurrence_id,
        }
    }
}

impl Div {
    pub fn new(left: Obj, right: Obj) -> Self {
        Self::new_with_source_occurrence_id(left, right, None)
    }

    pub fn new_with_source_occurrence_id(
        left: Obj,
        right: Obj,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        Div {
            left: Box::new(left),
            right: Box::new(right),
            source_occurrence_id,
        }
    }
}

impl Mod {
    pub fn new(left: Obj, right: Obj) -> Self {
        Mod {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Quot {
    pub fn new(left: Obj, right: Obj) -> Self {
        Quot {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Gcd {
    pub fn new(left: Obj, right: Obj) -> Self {
        Gcd {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Lcm {
    pub fn new(left: Obj, right: Obj) -> Self {
        Lcm {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Pow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        Pow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}
