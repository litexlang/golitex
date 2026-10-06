mod result;
mod verify_forall_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    AssumeDomFactResult, ProveAndStoreThenFactResult,
    VerifyForallFactFailed, VerifyForallFactResult,
    VerifyForallFactProof, VerifyKnownForallFactProof, ForallParameterRenaming,
    VerifyEmptyParameterDomainForallProof,
};
pub use well_defined_result::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
    VerifyForallFactWellDefinedResult,
};

mod source_fact_alpha;
