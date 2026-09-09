use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct ChainFactWellDefinedProof2 {
    pub well_defined_of_each_comparison: Vec<AtomicFactWellDefinedProof2>,
}

impl Runtime {
    pub fn verify_chain_fact_well_definedness2(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState2,
    ) -> Result<ChainFactWellDefinedProof2, RuntimeError> {
        let comparisons = fact.facts()?;
        let mut well_defined_of_each_comparison = Vec::new();
        for comparison in comparisons.iter() {
            well_defined_of_each_comparison.push(
                self.verify_atomic_fact_well_definedness2(comparison, verify_state.clone())?,
            );
        }
        Ok(ChainFactWellDefinedProof2 {
            well_defined_of_each_comparison,
        })
    }
}
