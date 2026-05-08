use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByFnSetAsSetStmt {
    pub func: Obj,
    pub fn_set: FnSet,
    pub line_file: LineFile,
}

impl fmt::Display for ByFnSetAsSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}{} {} {}{} {}",
            BY, FN_LOWER_CASE, SET, AS, SET, COLON, self.func, FACT_PREFIX, IN, self.fn_set
        )
    }
}

impl ByFnSetAsSetStmt {
    pub fn new(func: Obj, fn_set: FnSet, line_file: LineFile) -> Self {
        ByFnSetAsSetStmt {
            func,
            fn_set,
            line_file,
        }
    }
}

// view fn set as a subset of a cartesian product set
#[derive(Clone)]
pub struct ByFnAsSetStmt {
    pub function: Obj,
    pub line_file: LineFile,
}

/// Introduce facts from the built-in ordered-pair / tuple encoding.
#[derive(Clone)]
pub struct ByTupleAsSetStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

impl fmt::Display for ByFnAsSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}{} {}",
            BY, FN_LOWER_CASE, AS, SET, COLON, self.function
        )
    }
}

impl ByFnAsSetStmt {
    pub fn new(function: Obj, line_file: LineFile) -> Self {
        ByFnAsSetStmt {
            function,
            line_file,
        }
    }
}

impl fmt::Display for ByTupleAsSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}{} {}", BY, TUPLE, AS, SET, COLON, self.obj)
    }
}

impl ByTupleAsSetStmt {
    pub fn new(obj: Obj, line_file: LineFile) -> Self {
        ByTupleAsSetStmt { obj, line_file }
    }
}
