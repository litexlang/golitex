//! Complex-number projections and magnitude.

use crate::prelude::*;

#[derive(Clone)]
pub struct RealPart {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct ImaginaryPart {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct ComplexAbs {
    pub arg: Box<Obj>,
}

impl RealPart {
    pub fn new(arg: Obj) -> Self {
        RealPart { arg: Box::new(arg) }
    }
}

impl ImaginaryPart {
    pub fn new(arg: Obj) -> Self {
        ImaginaryPart { arg: Box::new(arg) }
    }
}

impl ComplexAbs {
    pub fn new(arg: Obj) -> Self {
        ComplexAbs { arg: Box::new(arg) }
    }
}
