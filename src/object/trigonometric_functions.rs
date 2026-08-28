//! Trigonometric function objects.

use crate::prelude::*;

#[derive(Clone)]
pub struct Sin {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Arcsin {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Cos {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Tan {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Cot {
    pub arg: Box<Obj>,
}

impl Sin {
    pub fn new(arg: Obj) -> Self {
        Sin { arg: Box::new(arg) }
    }
}

impl Arcsin {
    pub fn new(arg: Obj) -> Self {
        Arcsin { arg: Box::new(arg) }
    }
}

impl Cos {
    pub fn new(arg: Obj) -> Self {
        Cos { arg: Box::new(arg) }
    }
}

impl Tan {
    pub fn new(arg: Obj) -> Self {
        Tan { arg: Box::new(arg) }
    }
}

impl Cot {
    pub fn new(arg: Obj) -> Self {
        Cot { arg: Box::new(arg) }
    }
}
