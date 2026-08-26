use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByStructDefStmt {
    pub obj: Obj,
    pub struct_obj: StructObj,
    pub line_file: LineFile,
}

impl ByStructDefStmt {
    pub fn new(obj: Obj, struct_obj: StructObj, line_file: LineFile) -> Self {
        Self {
            obj,
            struct_obj,
            line_file,
        }
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
