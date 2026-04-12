mod error;

pub use error::{
    ArithmeticRuntimeError, ConflictMsg, DefineParamsRuntimeError, InstantiateRuntimeError,
    InferRuntimeError, NameAlreadyUsedRuntimeError, NewAtomicFactRuntimeError, ParseRuntimeError,
    RuntimeError, RuntimeErrorStruct, StoreFactRuntimeError, UnknownRuntimeError,
    VerifyRuntimeError, WellDefinedRuntimeError,
};
