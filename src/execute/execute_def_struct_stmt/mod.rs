//! Concrete `struct` definition execution.

mod exec_def_struct_stmt;
mod store_struct_definition_facts;

pub use exec_def_struct_stmt::{
    ExecDefStructFieldScopeSuccessResult, ExecDefStructStmtFailed, ExecDefStructStmtResult,
    ExecDefStructStmtSuccessResult,
};
