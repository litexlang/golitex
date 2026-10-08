//! Actual legal-base evidence for the four multiplicative logarithm laws.
use crate::execute::execute_fact_stmt::VerifyFactResult;

// These are alternative sufficient guards, not manufactured nonunit proofs.
// Example: a<1 with 0<a permits log(a,x*y)=log(a,x)+log(a,y).
pub enum LogAlgebraBaseProof {
    GreaterThanOne(VerifyFactResult),
    BelowOne(LogAlgebraBelowOneProof),
    PositiveNonunit(LogAlgebraPositiveNonunitProof),
}

pub struct LogAlgebraBelowOneProof {
    pub positive_proof: VerifyFactResult,
    pub less_than_one_proof: VerifyFactResult,
}
impl LogAlgebraBelowOneProof {
    pub fn new(positive_proof: VerifyFactResult, less_than_one_proof: VerifyFactResult) -> Self {
        Self {
            positive_proof,
            less_than_one_proof,
        }
    }
}

pub struct LogAlgebraPositiveNonunitProof {
    pub positive_proof: VerifyFactResult,
    pub nonunit_proof: VerifyFactResult,
}
impl LogAlgebraPositiveNonunitProof {
    pub fn new(positive_proof: VerifyFactResult, nonunit_proof: VerifyFactResult) -> Self {
        Self {
            positive_proof,
            nonunit_proof,
        }
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/log_algebra_base/tests.rs"]
mod log_algebra_base_tests;
