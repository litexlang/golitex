//! Well-definedness and inference annotations.

use crate::prelude::*;

impl StmtResult {
    pub fn with_fact_well_definedness(
        mut self,
        well_definedness: SuccessVerifyFactWellDefinedResult,
    ) -> Self {
        if let Some(success) = self.factual_success_mut() {
            success.well_definedness = well_definedness;
        }
        self
    }

    pub fn fact_id(&self) -> Option<FactId> {
        self.factual_success().and_then(|success| success.fact_id)
    }

    pub fn with_infers(mut self, infer_result: SuccessInferResult) -> Self {
        if let Some(success) = self.factual_success_mut() {
            success.infers.new_infer_result_inside(infer_result);
        } else if let StmtResult::Success(success) = &mut self {
            if let Some(common) = success.common_mut() {
                common.infers.new_infer_result_inside(infer_result);
            }
        }
        self
    }
}
