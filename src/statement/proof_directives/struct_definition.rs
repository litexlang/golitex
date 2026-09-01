use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByStructDefStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

impl ByStructDefStmt {
    pub fn new(obj: Obj, line_file: LineFile) -> Self {
        Self { obj, line_file }
    }

    pub fn store_reason() -> &'static str {
        "by struct def"
    }
}

impl fmt::Display for ByStructDefStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", BY, STRUCT, DEF, self.obj)
    }
}
