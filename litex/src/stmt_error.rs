// Re-export error types so that `use stmt_error::*` and `crate::stmt_error::*` work.
pub use crate::errors::{
    ArithmeticError, ExecError, NewAtomicFactError, ParseBlockError, ParsingError, StoreFactError,
    StmtError,
};
