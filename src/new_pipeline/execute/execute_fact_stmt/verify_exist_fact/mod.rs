mod helper;
mod result;
mod verify_exist_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    VerifyExistFactFailed, VerifyExistFactResult, VerifyExistUniqueFactResult,
    VerifyNotExistFactResult, VerifyPlainExistFactResult, VerifyPlainExistFactSuccess,
};
pub use well_defined_result::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
    VerifyExistFactWellDefinedResult,
};
