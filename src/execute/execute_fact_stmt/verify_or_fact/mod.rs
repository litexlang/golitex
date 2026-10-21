mod helper;
mod result;
mod search_or_fact_proof_by_builtin_rule;
mod verify_or_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    AssumeNegatedOrBranchResult, OrBuiltinRealLineTrichotomyEqLessGreater,
    OrBuiltinRealLineTrichotomyGreaterEqLess, OrBuiltinRealLineTrichotomyLessEqGreater,
    OrFactSearchProofByBuiltinRule, OrFactSearchProofByKnownOrFact,
    OrFactSearchProofBySelectedBranch, OrFactSearchedProof, VerifyOrFactFailed, VerifyOrFactResult,
    VerifyOrFactSuccess,
};
pub use well_defined_result::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof, VerifyOrFactWellDefinedResult,
};

pub(crate) use result::OrBuiltinAbsSignSplit;
pub(crate) use result::OrBuiltinClassicalImplication;
pub(crate) use result::OrBuiltinComplementaryAtomic;
pub(crate) use result::OrBuiltinCompleteResidues;
pub(crate) use result::OrBuiltinEqualityPlusStrictCoversWeak;
pub(crate) use result::OrBuiltinGreaterOrLessEqual;
pub(crate) use result::OrBuiltinIntegerDiscreteSplit;
pub(crate) use result::OrBuiltinIntegerSuccessorTail;
pub(crate) use result::OrBuiltinLessOrGreaterEqual;
pub(crate) use result::OrBuiltinNaturalZeroOrAtLeastOne;
pub(crate) use result::OrBuiltinSquareSumComponentNonzero;
pub(crate) use result::OrBuiltinWeakOrderLeOrGe;
pub(crate) use result::OrBuiltinZeroProductSplit;
