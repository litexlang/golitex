//! Rounding and binary extrema operations.

use crate::prelude::*;

#[derive(Clone)]
pub struct Floor {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Ceil {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Min {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Max {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

impl Floor {
    pub fn new(arg: Obj) -> Self {
        Floor { arg: Box::new(arg) }
    }
}

impl Ceil {
    pub fn new(arg: Obj) -> Self {
        Ceil { arg: Box::new(arg) }
    }
}

impl Min {
    pub fn new(left: Obj, right: Obj) -> Self {
        Min {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Max {
    pub fn new(left: Obj, right: Obj) -> Self {
        Max {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}
