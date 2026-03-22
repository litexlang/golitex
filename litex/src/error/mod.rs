mod error;

pub use error::{
    duplicate_used_name_error_message, ArithmeticError, ExecStmtError, InferError,
    NewAtomicFactError, ParseBlockError, ParsingError, StmtError, StoreFactError, UnknownError,
    VerifyError, WellDefinedError,
};
