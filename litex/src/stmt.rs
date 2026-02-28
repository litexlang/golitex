use std::fmt;
use crate::fact::Fact;
use crate::definitions::DefStmt;
pub enum Stmt {
    Fact(Fact),
    DefStmt(DefStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(fact) => write!(f, "{}", fact),
            Stmt::DefStmt(def_stmt) => write!(f, "{}", def_stmt),
        }
    }
}

/// 从 Stmt 取得 line 与 file_index（仅用于 Display 等）
pub fn line_file(stmt: &Stmt) -> (u32, usize) {
    match stmt {
        Stmt::Fact(fact) => fact.line_file(),
        Stmt::DefStmt(def_stmt) => def_stmt.line_file(),
    }
}