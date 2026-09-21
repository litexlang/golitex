use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ReleaseStructDefStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

impl ReleaseStructDefStmt {
    pub fn new(obj: Obj, line_file: LineFile) -> Self {
        Self { obj, line_file }
    }

    pub fn store_reason() -> &'static str {
        "release struct def"
    }
}

impl fmt::Display for ReleaseStructDefStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", RELEASE, STRUCT, DEF, self.obj)
    }
}
