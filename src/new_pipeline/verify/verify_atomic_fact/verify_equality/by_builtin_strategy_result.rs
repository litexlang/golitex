use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum EqualitySearchProofByBuiltinStrategy2 {
    ExtremumEquality(ExtremumEqualityStrategySingleStep2),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep2),
    ModCongruence(ModCongruenceStrategySingleStep2),
}

pub struct ExtremumEqualityStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

pub struct FiniteSetProductPointwiseEqualityStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

pub struct ModCongruenceStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}
