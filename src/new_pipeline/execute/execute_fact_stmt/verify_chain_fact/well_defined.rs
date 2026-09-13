use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct ChainFactWellDefinedProof {
    pub well_defined_of_each_comparison: Vec<DraftAtomicFactWellDefinedProof>,
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
                self.verify_draft_atomic_fact_well_definedness(comparison, verify_state.clone())?,
            );
        }
        Ok(ChainFactWellDefinedProof {
            well_defined_of_each_comparison,
        })
    }
}
