mod error;

pub use error::{
    ArithmeticRuntimeError, DefineParamsRuntimeError, InferRuntimeError, InstantiateRuntimeError,
    NameAlreadyUsedRuntimeError, NewAtomicFactRuntimeError, ParseRuntimeError, RuntimeError,
    RuntimeErrorStruct, StoreFactRuntimeError, UnknownRuntimeError, VerifyRuntimeError,
    WellDefinedRuntimeError,
};
