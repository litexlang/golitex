use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferExistUniqueFactResult, InferExistUniqueUniquenessForallResult,
};

impl Runtime {
    pub(crate) fn infer_exist_unique_fact(
        &mut self,
        plain: &PlainExistFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<InferExistUniqueFactResult> {
        let n: usize = plain
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum();
        if n == 0 {
            return Ok(InferExistUniqueFactResult::NoInfer);
        }
        let uniqueness = self.build_exist_unique_component_uniqueness_forall_fact(plain)?;
        let derived = Box::new(self.store_inferred_fact(&Fact::ForallFact(uniqueness))?);
        Ok(InferExistUniqueFactResult::UniquenessForall(
            InferExistUniqueUniquenessForallResult { derived },
        ))
    }
}
