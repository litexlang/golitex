mod result;
mod verify_forall_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    AssumeDomFactResult, ForallParameterRenaming, ProveAndStoreThenFactResult,
    VerifyEmptyParameterDomainForallProof, VerifyForallFactFailed, VerifyForallFactProof,
    VerifyForallFactResult, VerifyForallFactSuccess, VerifyKnownForallFactProof,
};
pub use well_defined_result::{
    CompactForallFactWellDefinedProof, DetailedForallFactWellDefinedProof,
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
    NormalForallFactWellDefinedProof, VerifyForallFactWellDefinedResult,
};

mod source_fact_alpha;
