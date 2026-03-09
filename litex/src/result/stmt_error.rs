// Re-export error types so that `use result::*` includes these.
pub use crate::error::{
    ArithmeticError, ExecError, NewAtomicFactError, ParseBlockError, ParsingError, StoreFactError,
    StmtError, UnknownError, VerifyFactError, WellDefinedError,
};
