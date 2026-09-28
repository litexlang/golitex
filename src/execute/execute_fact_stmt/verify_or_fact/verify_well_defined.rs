use crate::ast::fact::{AndChainAtomicFact, OrFact};
use crate::execute::execute_fact_stmt::verify_or_fact::well_defined_result::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof, VerifyOrFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::VerifyFactWellDefinedResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // WD each AndChainAtomic branch via fine-grained atomic/and/chain WD.
    // First soft miss → Failed.
    pub fn verify_or_fact_well_definedness(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyOrFactWellDefinedResult> {
        let mut succeeded_branches = Vec::with_capacity(fact.facts.len());
        for (failed_index, branch) in fact.facts.iter().enumerate() {
            match self.verify_and_chain_atomic_fact_well_definedness(branch, verify_state.clone())?
            {
                VerifyFactWellDefinedResult::Success(proof) => {
                    succeeded_branches.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(failed_branch) => {
                    return Ok(VerifyOrFactWellDefinedResult::Failed(
                        FailToVerifyOrFactWellDefinedResult {
                            failed_index,
                            succeeded_branches,
                            failed_branch: Box::new(failed_branch),
                        },
                    ));
                }
            }
        }
        Ok(VerifyOrFactWellDefinedResult::Success(
            OrFactWellDefinedProof {
                branches: succeeded_branches,
            },
        ))
    }
}

impl Runtime {
    // AndChainAtomicFact is only atomic / and / chain — call the matching WD entry.
    fn verify_and_chain_atomic_fact_well_definedness(
        &mut self,
        branch: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        match branch {
            AndChainAtomicFact::AtomicFact(atomic) => {
                self.wrap_atomic_fact_wd(atomic, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => self.wrap_and_fact_wd(and_fact, verify_state),
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.wrap_chain_fact_wd(chain_fact, verify_state)
            }
        }
    }
}
