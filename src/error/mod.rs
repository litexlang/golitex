mod error;

pub use error::{
    short_exec_error, ArithmeticRuntimeError, DefineParamsRuntimeError,
    InferRuntimeError, InstantiateRuntimeError, NameAlreadyUsedRuntimeError,
    NewFactRuntimeError, ParseRuntimeError, RuntimeError, RuntimeErrorStruct,
    StoreFactRuntimeError, UnknownRuntimeError, VerifyRuntimeError, WellDefinedRuntimeError,
};
