mod error;

pub use error::{
    exec_stmt_error_with_stmt_and_cause, short_exec_error, ArithmeticRuntimeError,
    DefineParamsRuntimeError, InferRuntimeError, InstantiateRuntimeError,
    NameAlreadyUsedRuntimeError, NewFactRuntimeError, ParseRuntimeError, RuntimeError,
    RuntimeErrorStruct, StoreFactRuntimeError, UnknownRuntimeError, VerifyRuntimeError,
    WellDefinedRuntimeError,
};
