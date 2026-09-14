use crate::new_pipeline::ast::fact::ChainFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyChainFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Exact ByCache is handled in `verify_fact` before this entry.
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyChainFactResult>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
