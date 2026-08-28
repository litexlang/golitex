//! Elementary scalar functions.

use crate::prelude::*;

#[derive(Clone)]
pub struct Sqrt {
    pub arg: Box<Obj>,
}

/// Real exponential `e^x`.
#[derive(Clone)]
pub struct Exp {
    pub arg: Box<Obj>,
}

/// Natural logarithm on the positive reals.
#[derive(Clone)]
pub struct Ln {
    pub arg: Box<Obj>,
}

/// Real sign function with values `-1`, `0`, and `1`.
#[derive(Clone)]
pub struct Sign {
    pub arg: Box<Obj>,
}

/// Natural-number factorial.
#[derive(Clone)]
pub struct Factorial {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Abs {
    pub arg: Box<Obj>,
}

/// Real logarithm `log(base, x)` with `base > 0`, `base != 1`, `x > 0`.
#[derive(Clone)]
pub struct Log {
    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

impl Exp {
    pub fn new(arg: Obj) -> Self {
        Exp { arg: Box::new(arg) }
    }
}

impl Ln {
    pub fn new(arg: Obj) -> Self {
        Ln { arg: Box::new(arg) }
    }
}

impl Sign {
    pub fn new(arg: Obj) -> Self {
        Sign { arg: Box::new(arg) }
    }
}

impl Factorial {
    pub fn new(arg: Obj) -> Self {
        Factorial { arg: Box::new(arg) }
    }
}

impl Abs {
    pub fn new(arg: Obj) -> Self {
        Abs { arg: Box::new(arg) }
    }
}

impl Sqrt {
    pub fn new(arg: Obj) -> Self {
        Sqrt { arg: Box::new(arg) }
    }
}

impl Log {
    pub fn new(base: Obj, arg: Obj) -> Self {
        Log {
            base: Box::new(base),
            arg: Box::new(arg),
        }
    }
}
