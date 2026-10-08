use crate::ast::fact::{exist_shaped_fact_to_fact, NotForallFact};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferNotForallFactResult;

impl Runtime {
    // Shape rewrite (not atomic packaging): De Morgan counterexample exist, then store_inferred.
    // Example: `not forall x R: x > 0` → also store `exist x R st {not x > 0}`.
    pub(crate) fn infer_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<InferNotForallFactResult> {
        let Some(derived_exist) = self.not_forall_to_counterexample_exist(not_forall)? else {
            return Err(crate::runtime::RuntimeError::InternalBug(
                "infer not forall: cannot negate body into exist counterexample".to_string(),
            ));
        };
        let derived_exist = Box::new(self.store_inferred_fact_and_infer(
            &exist_shaped_fact_to_fact(&derived_exist),
            verify_state,
        )?);
        Ok(InferNotForallFactResult { derived_exist })
    }
}
