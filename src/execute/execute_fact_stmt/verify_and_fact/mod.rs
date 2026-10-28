mod result;
mod verify_and_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{VerifyAndFactFailed, VerifyAndFactResult};
pub use well_defined_result::{
    AndFactWellDefinedProof, CompactAndFactWellDefinedProof, DetailedAndFactWellDefinedProof,
    FailToVerifyAndFactWellDefinedResult, NormalAndFactWellDefinedProof,
    VerifyAndFactWellDefinedResult,
};

pub(crate) use result::VerifyAndFactSuccess;
