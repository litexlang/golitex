use crate::new_pipeline::ast::fact::NotForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::result::{
    not_forall_fact_result_from_exist_fail, not_forall_fact_result_from_success,
    not_forall_fact_result_from_unsupported,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove `not forall` by De Morgan counterexample exist, then verify that exist.
    // Example:
    //   trust exist x R st {not x > 0}
    //   not forall x R:
    //       x > 0
    pub fn verify_not_forall_fact(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let Some(derived_exist) = self.not_forall_to_counterexample_exist(fact)? else {
            return Ok(not_forall_fact_result_from_unsupported(fact));
        };
        let prove_derived_exist = self.verify_exist_shaped_fact(&derived_exist, verify_state)?;
        if prove_derived_exist.is_failed() {
            return Ok(not_forall_fact_result_from_exist_fail(
                fact,
                derived_exist,
                prove_derived_exist,
            ));
        }
        Ok(not_forall_fact_result_from_success(
            fact,
            derived_exist,
            prove_derived_exist,
        ))
    }
}
