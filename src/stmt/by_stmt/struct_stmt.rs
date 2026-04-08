use crate::prelude::*;
use std::fmt;

/// 由 struct 定义与类型实参，生成「实例集合」的刻画：与 `family p(R) = …` 的 `by family` 对偶。
#[derive(Clone)]
pub struct ByStructStmt {
    pub struct_obj: Obj,
    pub line_file: LineFile,
}

impl fmt::Display for ByStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", BY, STRUCT, COLON, self.struct_obj)
    }
}

impl ByStructStmt {
    pub fn new(struct_obj: Obj, line_file: LineFile) -> Self {
        ByStructStmt {
            struct_obj,
            line_file,
        }
    }
}
