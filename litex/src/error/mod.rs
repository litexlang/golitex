mod error;

pub use error::{
    duplicate_used_name_error_msg_without_line_file, ArithmeticError, DefineParamsError,
    ExecStmtError, InferError, NameAlreadyUsedError, NewAtomicFactError, ParseBlockError,
    ParsingError, RuntimeError, StoreFactError, VerifyError, UnknownError, WellDefinedError,
};
