mod by_bijective_preimage;
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

pub(crate) use result::ExistShapedBuiltinArchimedeanReciprocal;
pub(crate) use result::ExistShapedBuiltinBijectivePreimage;
pub(crate) use result::ExistShapedBuiltinEqualityWitnessFromMembership;
pub(crate) use result::ExistShapedBuiltinIntegerMultipleFromZeroRemainder;
pub(crate) use result::ExistShapedBuiltinNonemptySetMemberWitness;
pub(crate) use result::ExistShapedBuiltinRationalIntegerRatio;
pub(crate) use result::ExistShapedBuiltinRationalPositiveDenominator;
pub(crate) use result::ExistShapedBuiltinRealDensityMidpoint;
pub(crate) use result::ExistShapedBuiltinRealLineComparisonWitness;
pub(crate) use result::ExistShapedFactSearchProofByKnownExistShapedFact;
pub(crate) use result::VerifyNotExistFactSuccess;
