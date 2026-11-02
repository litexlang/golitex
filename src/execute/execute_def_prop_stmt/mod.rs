//! Concrete `prop` definition execution.

mod exec_def_prop_stmt;

pub use exec_def_prop_stmt::{
    DefPropLocalFailed, ExecDefPropLocalFailure, ExecDefPropStmtFailed, ExecDefPropStmtResult,
    ExecDefPropStmtSuccessResult,
};
