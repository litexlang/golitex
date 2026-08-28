//! Well-definedness, inference, and execution-trace annotations.

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

    pub fn with_execution_trace(mut self, trace: StatementExecutionTrace) -> Self {
        if let Some(success) = self.factual_success_mut() {
            success.execution_trace = Some(trace);
        } else if let StmtResult::Success(success) = &mut self {
            if let Some(common) = success.common_mut() {
                common.execution_trace = Some(trace);
            }
        }
        self
    }

    pub fn execution_trace(&self) -> Option<&StatementExecutionTrace> {
        if let Some(success) = self.factual_success() {
            success.execution_trace.as_ref()
        } else if let StmtResult::Success(success) = self {
            success
                .common()
                .and_then(|common| common.execution_trace.as_ref())
        } else {
            None
        }
    }
}
