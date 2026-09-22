use crate::new_pipeline::ast::fact::OrFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferOrFactResult;

impl Runtime {
    // Or is stored whole (branches are not split). Eager infer on a disjunct would
    // assert a branch that was never proved — intentionally NoInfer.
    pub(crate) fn infer_or_fact(&mut self, _or_fact: &OrFact) -> RuntimeResult<InferOrFactResult> {
        Ok(InferOrFactResult::NoInfer)
    }
}
