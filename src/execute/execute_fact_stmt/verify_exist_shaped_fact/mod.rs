mod helper;
mod result;
mod verify_exist_shaped_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    ExistShapedFactSearchProofByBuiltinRule, ExistShapedFactSearchedProof,
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyExistUniqueFactResult,
    VerifyExistUniqueFactSuccess, VerifyNotExistFactResult, VerifyPlainExistFactResult,
    VerifyPlainExistFactSuccess,
};
pub use well_defined_result::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
    VerifyExistShapedFactWellDefinedResult,
};
mod align_exist_conclusion;
