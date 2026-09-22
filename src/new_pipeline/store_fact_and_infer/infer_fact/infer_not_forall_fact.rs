use crate::new_pipeline::ast::fact::NotForallFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferFactResult;

impl Runtime {
    // NotForall: De Morgan counterexample exist into known_exist.
    // Example: `not forall x R: x > 0` → also store `exist x R st {not x > 0}`.
    pub(crate) fn infer_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
    ) -> RuntimeResult<InferFactResult> {
        let Some(derived_exist) = self.not_forall_to_counterexample_exist(not_forall)? else {
            return Err(crate::new_pipeline::runtime::RuntimeError::InternalBug(
                "infer not forall: cannot negate body into exist counterexample".to_string(),
            ));
        };
        let derived_exist = self.store_exist_shaped_fact(&derived_exist)?;
        Ok(InferFactResult::NotForallFact { derived_exist })
    }
}
