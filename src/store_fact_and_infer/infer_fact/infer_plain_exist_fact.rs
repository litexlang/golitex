use crate::prelude::*;
use crate::store_fact_and_infer::InferPlainExistFactResult;

impl Runtime {
    pub(crate) fn infer_plain_exist_fact(
        &mut self,
        _fact: &PlainExistFact,
    ) -> RuntimeResult<InferPlainExistFactResult> {
        Ok(InferPlainExistFactResult::NoInfer)
    }
}
