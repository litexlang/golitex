use crate::prelude::*;
use crate::verify_rewrite::VerifyState;
use crate::verify_rewrite::FactStmt;

pub enum EqualitySearchProofByBuiltinStrategy {
    ExtremumEquality(ExtremumEqualityStrategySingleStep),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep),
    ModCongruence(ModCongruenceStrategySingleStep),
}

pub struct ExtremumEqualityStrategySingleStep {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct FiniteSetProductPointwiseEqualityStrategySingleStep {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct ModCongruenceStrategySingleStep {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
