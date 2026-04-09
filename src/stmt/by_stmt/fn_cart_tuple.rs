use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByFnSetStmt {
    pub func: Obj,
    pub fn_set: FnSet,
    pub line_file: LineFile,
}

impl fmt::Display for ByFnSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {} {}{} {}",
            BY,
            FN_LOWER_CASE,
            SET,
            COLON,
            self.func,
            FACT_PREFIX,
            IN,
            self.fn_set
        )
    }
}

impl ByFnSetStmt {
    pub fn new(func: Obj, fn_set: FnSet, line_file: LineFile) -> Self {
        ByFnSetStmt {
            func,
            fn_set,
            line_file,
        }
    }
}

// view fn set as a subset of a cartesian product set
#[derive(Clone)]
pub struct ByFnStmt {
    pub function: Obj,
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
        write!(f, "{} {}{} {}", BY, FN_LOWER_CASE, COLON, self.function)
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
