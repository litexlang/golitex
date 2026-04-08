use crate::prelude::*;
use std::fmt;

/// 由 family 定义与具体类型实参，建立 `family name(args)` 与实例化后集合（`equal_to`）的等式。
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
