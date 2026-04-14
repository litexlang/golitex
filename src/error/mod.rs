mod error;

pub use error::{
    short_exec_error, ArithmeticRuntimeError, DefineParamsRuntimeError,
    InferRuntimeError, InstantiateRuntimeError, NameAlreadyUsedRuntimeError,
    NewAtomicFactRuntimeError, ParseRuntimeError, RuntimeError, RuntimeErrorStruct,
    StoreFactRuntimeError, UnknownRuntimeError, VerifyRuntimeError, WellDefinedRuntimeError,
};
