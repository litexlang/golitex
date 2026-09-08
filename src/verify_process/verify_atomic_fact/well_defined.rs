use crate::prelude::*;

pub struct VerifyAtomicFactWellDefinednessResult {
    pub well_definedness_proof_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}
