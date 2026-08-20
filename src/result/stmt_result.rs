use crate::prelude::*;

/// The canonical result of executing one Litex statement.
///
#[derive(Debug)]
pub enum StmtResult {
    Success(SuccessStmtResult),
    Unknown(UnknownStmtResult),
}

#[derive(Debug)]
pub enum UnknownStmtResult {
    Generic(Box<UnknownGenericStmtResult>),
    Fact(Box<UnknownFactResult>),
}

impl From<SuccessStmtResult> for StmtResult {
    fn from(success: SuccessStmtResult) -> Self {
        StmtResult::Success(success)
    }
}

impl From<SuccessFactStmtResult> for StmtResult {
    fn from(success: SuccessFactStmtResult) -> Self {
        StmtResult::Success(SuccessStmtResult::Fact(Box::new(success)))
    }
}

impl From<SuccessUnsafeStmtResult> for StmtResult {
    fn from(success: SuccessUnsafeStmtResult) -> Self {
        SuccessStmtResult::UnsafeStmt(success).into()
    }
}

impl From<SuccessDefObjStmtResult> for StmtResult {
    fn from(success: SuccessDefObjStmtResult) -> Self {
        SuccessStmtResult::DefObjStmt(success).into()
    }
}

impl From<SuccessDefPredicateStmtResult> for StmtResult {
    fn from(success: SuccessDefPredicateStmtResult) -> Self {
        SuccessStmtResult::DefPredicateStmt(success).into()
    }
}

impl From<SuccessDefInterfaceStmtResult> for StmtResult {
    fn from(success: SuccessDefInterfaceStmtResult) -> Self {
        SuccessStmtResult::DefInterfaceStmt(success).into()
    }
}

impl From<SuccessByStmtResult> for StmtResult {
    fn from(success: SuccessByStmtResult) -> Self {
        SuccessStmtResult::By(success).into()
    }
}

impl From<SuccessWitnessStmtResult> for StmtResult {
    fn from(success: SuccessWitnessStmtResult) -> Self {
        SuccessStmtResult::Witness(success).into()
    }
}

impl From<SuccessProofBlockStmtResult> for StmtResult {
    fn from(success: SuccessProofBlockStmtResult) -> Self {
        SuccessStmtResult::ProofBlock(success).into()
    }
}

impl From<SuccessCommandStmtResult> for StmtResult {
    fn from(success: SuccessCommandStmtResult) -> Self {
        SuccessStmtResult::Command(success).into()
    }
}

impl From<UnknownGenericStmtResult> for StmtResult {
    fn from(unknown: UnknownGenericStmtResult) -> Self {
        StmtResult::Unknown(UnknownStmtResult::Generic(Box::new(unknown)))
    }
}

impl From<UnknownFactResult> for StmtResult {
    fn from(unknown: UnknownFactResult) -> Self {
        StmtResult::Unknown(UnknownStmtResult::Fact(Box::new(unknown)))
    }
}

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

    pub fn statement(&self) -> Option<Stmt> {
        match self {
            StmtResult::Success(success) => Some(success.statement()),
            StmtResult::Unknown(_) => None,
        }
    }

    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        match self {
            StmtResult::Success(success) => success.statement().line_file(),
            StmtResult::Unknown(UnknownStmtResult::Fact(unknown)) => unknown.goal().line_file(),
            StmtResult::Unknown(UnknownStmtResult::Generic(_)) => default_line_file(),
        }
    }

    pub fn is_true(&self) -> bool {
        !self.is_unknown()
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, StmtResult::Unknown(_))
    }

    pub fn as_unknown(&self) -> Option<&UnknownGenericStmtResult> {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Generic(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn as_fact_unknown(&self) -> Option<&UnknownFactResult> {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Fact(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn wrap_unknown_for_fact(self, fact: Fact) -> Self {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Generic(unknown)) => {
                UnknownFactResult::from_stmt_unknown(fact, *unknown).into()
            }
            other => other,
        }
    }

    pub fn factual_success(&self) -> Option<&SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(success.as_ref()),
            _ => None,
        }
    }

    pub fn factual_success_mut(&mut self) -> Option<&mut SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(success.as_mut()),
            _ => None,
        }
    }

    pub fn infer_result(&self) -> SuccessInferResult {
        if let Some(success) = self.factual_success() {
            success.infers.clone()
        } else if let StmtResult::Success(success) = self {
            success
                .common()
                .map(|common| common.infers.clone())
                .unwrap_or_else(SuccessInferResult::new)
        } else {
            SuccessInferResult::new()
        }
    }

    pub fn into_factual_success(self) -> Option<SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(*success),
            _ => None,
        }
    }

    pub fn non_factual_success(&self) -> Option<&SuccessStmtResult> {
        match self {
            StmtResult::Success(success @ SuccessStmtResult::UnsafeStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefObjStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefPredicateStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefInterfaceStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefAlgoStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefThmStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::AxiomStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefStrategyStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::By(_))
            | StmtResult::Success(success @ SuccessStmtResult::Witness(_))
            | StmtResult::Success(success @ SuccessStmtResult::ProofBlock(_))
            | StmtResult::Success(success @ SuccessStmtResult::Command(_)) => Some(success),
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }

    pub fn non_factual_success_mut(&mut self) -> Option<&mut SuccessStmtResult> {
        match self {
            StmtResult::Success(success @ SuccessStmtResult::UnsafeStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefObjStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefPredicateStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefInterfaceStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefAlgoStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefThmStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::AxiomStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefStrategyStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::By(_))
            | StmtResult::Success(success @ SuccessStmtResult::Witness(_))
            | StmtResult::Success(success @ SuccessStmtResult::ProofBlock(_))
            | StmtResult::Success(success @ SuccessStmtResult::Command(_)) => Some(success),
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }

    pub fn into_non_factual_success(self) -> Option<SuccessStmtResult> {
        match self {
            StmtResult::Success(success @ SuccessStmtResult::UnsafeStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefObjStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefPredicateStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefInterfaceStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefAlgoStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefThmStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::AxiomStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::DefStrategyStmt(_))
            | StmtResult::Success(success @ SuccessStmtResult::By(_))
            | StmtResult::Success(success @ SuccessStmtResult::Witness(_))
            | StmtResult::Success(success @ SuccessStmtResult::ProofBlock(_))
            | StmtResult::Success(success @ SuccessStmtResult::Command(_)) => Some(success),
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statement_result_stays_pointer_sized_enough_for_recursive_composition() {
        assert!(
            std::mem::size_of::<StmtResult>() <= 32,
            "StmtResult unexpectedly grew to {} bytes; large success payloads belong behind Box",
            std::mem::size_of::<StmtResult>()
        );
    }
}
