use crate::prelude::*;

pub struct ChainFactWellDefinedProof {
    pub well_defined_of_each_comparison: Vec<AtomicFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_chain_fact_well_definedness(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<ChainFactWellDefinedProof, RuntimeError> {
        let comparisons = fact.facts()?;
        let mut well_defined_of_each_comparison = Vec::new();
        for comparison in comparisons.iter() {
            well_defined_of_each_comparison.push(
                self.verify_atomic_fact_well_definedness(comparison, verify_state.clone())?,
            );
        }
        Ok(ChainFactWellDefinedProof {
            well_defined_of_each_comparison,
        })
    }
}
