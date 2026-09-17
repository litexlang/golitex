use crate::new_pipeline::ast::fact::AndFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::result::{
    and_fact_result_from_component_fail, and_fact_result_from_success,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove and by proving each atomic component.
    // Example: `1 < 2 and 2 < 3` requires proofs of `1 < 2` and `2 < 3`.
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let mut components = Vec::with_capacity(fact.facts.len());
        for (failed_index, atomic) in fact.facts.iter().enumerate() {
            let component = self.verify_atomic_fact(atomic, verify_state.clone())?;
            if component.is_failed() {
                return Ok(and_fact_result_from_component_fail(
                    fact,
                    failed_index,
                    components,
                    component,
                ));
            }
            components.push(component);
        }
        Ok(and_fact_result_from_success(fact, components))
    }
}
