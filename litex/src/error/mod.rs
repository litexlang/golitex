mod error;

pub use error::{
    duplicate_used_name_error_message, format_name_already_used_error_body, ArithmeticError,
    ExecStmtError, InferError, NameAlreadyUsedError, NewAtomicFactError, ParseBlockError,
    ParsingError, RuntimeError, StoreFactError, UnknownError, VerifyError, VerifyUnknownError,
    WellDefinedError,
};
