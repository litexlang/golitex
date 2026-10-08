use super::store_fact_and_infer_result::StoreFactAndInferResult;
use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Store by fact shape, then run local inference on that fact.
    // Callers already verified the seed fact; this path is not open-ended proof search.
    // Infer may only generate extra facts (see store_inferred_fact_and_infer for those).
    pub fn store_fact_and_infer(
        &mut self,
        fact: &Fact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<StoreFactAndInferResult> {
        let store = self.store_fact(fact)?;
        // The seed has passed WD at its caller's statement/local proof boundary.
        // Cache only its direct atomic subjects in this scope, never the bound
        // internals of a quantified fact. Exploratory verify does not record WD.
        if let Fact::AtomicFact(atomic) = fact {
            for obj in crate::ast::fact::atomic_fact_args_ref(atomic) {
                // Named objects have their own definition evidence. Recording
                // a second WD cache entry for each alias adds no certificate.
                if matches!(obj, crate::ast::obj::Obj::Identifier(_)) {
                    continue;
                }
                if self.well_defined_visible_in_stack(obj).is_none() {
                    let id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(obj.clone(), id);
                }
            }
        }
        let infer = self.infer_fact(fact, verify_state)?;
        Ok(StoreFactAndInferResult { store, infer })
    }
}
