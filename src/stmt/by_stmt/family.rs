use crate::prelude::*;
use std::fmt;

// From a `family` definition and type args, relate `\name(args)` to the instantiated `equal_to` set.
#[derive(Clone)]
pub struct ByFamilyStmt {
    pub family_obj: Obj,
    pub line_file: LineFile,
}

impl fmt::Display for ByFamilyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", BY, FAMILY, COLON, self.family_obj)
    }
}

impl ByFamilyStmt {
    pub fn new(family_obj: Obj, line_file: LineFile) -> Self {
        ByFamilyStmt {
            family_obj,
            line_file,
        }
    }
}
