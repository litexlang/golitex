use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferForallFactResult;

impl Runtime {
    // Forall is indexed for later use/instantiation. Do not eager-push then-facts
    // into the ambient env (that would ignore binders / dom).
    pub(crate) fn infer_forall_fact(
        &mut self,
        _forall: &ForallFact,
    ) -> RuntimeResult<InferForallFactResult> {
        Ok(InferForallFactResult::NoInfer)
    }
}
