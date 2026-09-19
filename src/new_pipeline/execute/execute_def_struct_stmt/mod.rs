//! Concrete `struct` definition execution.

mod exec_def_struct_stmt;

pub use exec_def_struct_stmt::{
    ExecDefStructFieldScopeSuccessResult, ExecDefStructStmtFailed, ExecDefStructStmtResult,
    ExecDefStructStmtSuccessResult,
};
