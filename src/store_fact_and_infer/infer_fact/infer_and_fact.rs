use crate::ast::fact::AndFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferAndFactResult;

impl Runtime {
    // Infer each atomic conjunct of an already-stored and-fact (true atomic packaging).
    // Example: stored `a $in {x R: x > 0} and b = cart(R, R)` runs atomic infer on both sides.
    pub(crate) fn infer_and_fact(&mut self, and_fact: &AndFact, verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<InferAndFactResult> {
        let mut components = Vec::with_capacity(and_fact.facts.len());
        for atomic in &and_fact.facts {
            components.push(self.infer_atomic_fact(atomic, verify_state)?);
        }
        Ok(InferAndFactResult { components })
    }
}
