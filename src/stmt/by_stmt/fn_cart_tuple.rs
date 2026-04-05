use crate::prelude::*;
use std::fmt;

// view fn set as a subset of a cartesian product set
#[derive(Clone)]
pub struct ByFnStmt {
    pub function: Obj,
    pub line_file: LineFile,
}

// view a cartesian product set as a set (ordered pairs)
#[derive(Clone)]
pub struct ByCartStmt {
    pub cart: Cart,
    pub line_file: LineFile,
}

/// Introduce facts from the built-in ordered-pair / tuple encoding.
#[derive(Clone)]
pub struct ByTupleStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

impl fmt::Display for ByFnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", BY, FN_FOR_FN_WITH_PARAMS, self.function)
    }
}

impl ByFnStmt {
    pub fn new(function: Obj, line_file: LineFile) -> Self {
        ByFnStmt {
            function,
            line_file,
        }
    }
}

impl fmt::Display for ByCartStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", BY, CART, self.cart)
    }
}

impl ByCartStmt {
    pub fn new(cart: Cart, line_file: LineFile) -> Self {
        ByCartStmt { cart, line_file }
    }
}

impl fmt::Display for ByTupleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", BY, TUPLE, COLON, self.obj)
    }
}

impl ByTupleStmt {
    pub fn new(obj: Obj, line_file: LineFile) -> Self {
        ByTupleStmt { obj, line_file }
    }
}
