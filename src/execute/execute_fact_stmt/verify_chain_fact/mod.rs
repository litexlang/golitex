mod result;
mod verify_chain_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{VerifyChainFactFailed, VerifyChainFactResult};
pub use well_defined_result::{
    ChainFactWellDefinedProof, CompactChainFactWellDefinedProof, DetailedChainFactWellDefinedProof,
    FailToVerifyChainFactWellDefinedResult, NormalChainFactWellDefinedProof,
    VerifyChainFactWellDefinedResult,
};

pub(crate) use result::VerifyChainFactSuccess;
