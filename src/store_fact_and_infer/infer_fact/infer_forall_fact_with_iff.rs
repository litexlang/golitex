use crate::ast::fact::ForallFactWithIff;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferForallFactWithIffResult;

impl Runtime {
    // Iff split into two forall directions is store_fact's job. Infer stays NoInfer;
    // those stored foralls do not get ambient atomic unpack either.
    pub(crate) fn infer_forall_fact_with_iff(
        &mut self,
        _forall_iff: &ForallFactWithIff,
    ) -> RuntimeResult<InferForallFactWithIffResult> {
        Ok(InferForallFactWithIffResult::NoInfer)
    }
}
