mod error;

pub use error::{
    duplicate_used_name_error_msg_without_line_file, DefineParamsError, ExecStmtError, InferError,
    NameAlreadyUsedError, ParseBlockError, ParsingError, RuntimeError, RuntimeErrorStruct,
    UnknownError, VerifyError, WellDefinedError,
};
