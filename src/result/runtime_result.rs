use crate::prelude::*;

/// The canonical result of executing one Litex statement.
///
#[derive(Debug)]
pub enum StmtResult {
    Success(VerifiedStmtIr),
    Unknown(UnknownStatementResult),
}

#[derive(Debug)]
pub enum UnknownStatementResult {
    Statement(StmtUnknown),
    Fact(FactUnknown),
}

impl From<VerifiedStmtIr> for StmtResult {
    fn from(success: VerifiedStmtIr) -> Self {
        StmtResult::Success(success)
    }
}

impl From<VerifiedFactStmtIr> for StmtResult {
    fn from(success: VerifiedFactStmtIr) -> Self {
        StmtResult::Success(VerifiedStmtIr::Fact(success))
    }
}

impl From<VerifiedUnsafeStmtIr> for StmtResult {
    fn from(success: VerifiedUnsafeStmtIr) -> Self {
        VerifiedStmtIr::UnsafeStmt(success).into()
    }
}

impl From<VerifiedDefObjStmtIr> for StmtResult {
    fn from(success: VerifiedDefObjStmtIr) -> Self {
        VerifiedStmtIr::DefObjStmt(success).into()
    }
}

impl From<VerifiedDefPredicateStmtIr> for StmtResult {
    fn from(success: VerifiedDefPredicateStmtIr) -> Self {
        VerifiedStmtIr::DefPredicateStmt(success).into()
    }
}

impl From<VerifiedDefInterfaceStmtIr> for StmtResult {
    fn from(success: VerifiedDefInterfaceStmtIr) -> Self {
        VerifiedStmtIr::DefInterfaceStmt(success).into()
    }
}

impl From<VerifiedByStmtIr> for StmtResult {
    fn from(success: VerifiedByStmtIr) -> Self {
        VerifiedStmtIr::By(success).into()
    }
}

impl From<VerifiedWitnessStmtIr> for StmtResult {
    fn from(success: VerifiedWitnessStmtIr) -> Self {
        VerifiedStmtIr::Witness(success).into()
    }
}

impl From<VerifiedProofBlockStmtIr> for StmtResult {
    fn from(success: VerifiedProofBlockStmtIr) -> Self {
        VerifiedStmtIr::ProofBlock(success).into()
    }
}

impl From<VerifiedCommandStmtIr> for StmtResult {
    fn from(success: VerifiedCommandStmtIr) -> Self {
        VerifiedStmtIr::Command(success).into()
    }
}

impl From<StmtUnknown> for StmtResult {
    fn from(unknown: StmtUnknown) -> Self {
        StmtResult::Unknown(UnknownStatementResult::Statement(unknown))
    }
}

impl From<FactUnknown> for StmtResult {
    fn from(unknown: FactUnknown) -> Self {
        StmtResult::Unknown(UnknownStatementResult::Fact(unknown))
    }
}

impl StmtResult {
    pub fn with_well_definedness_certificate(
        mut self,
        certificate: WellDefinednessCertificate,
    ) -> Self {
        if let StmtResult::Success(success) = &mut self {
            if let Some(fact) = success.fact_mut() {
                fact.well_definedness = certificate;
            } else if let Some(common) = success.common_mut() {
                common.well_definedness = certificate;
            }
        }
        self
    }

    pub fn fact_id(&self) -> Option<FactId> {
        self.factual_success().and_then(|success| success.fact_id)
    }

    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
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
            StmtResult::Unknown(UnknownStatementResult::Fact(unknown)) => {
                unknown.goal().line_file()
            }
            StmtResult::Unknown(UnknownStatementResult::Statement(_)) => default_line_file(),
        }
    }

    pub fn is_true(&self) -> bool {
        !self.is_unknown()
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, StmtResult::Unknown(_))
    }

    pub fn as_unknown(&self) -> Option<&StmtUnknown> {
        match self {
            StmtResult::Unknown(UnknownStatementResult::Statement(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn as_fact_unknown(&self) -> Option<&FactUnknown> {
        match self {
            StmtResult::Unknown(UnknownStatementResult::Fact(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn wrap_unknown_for_fact(self, fact: Fact) -> Self {
        match self {
            StmtResult::Unknown(UnknownStatementResult::Statement(unknown)) => {
                FactUnknown::from_stmt_unknown(fact, unknown).into()
            }
            other => other,
        }
    }

    pub fn factual_success(&self) -> Option<&VerifiedFactStmtIr> {
        match self {
            StmtResult::Success(VerifiedStmtIr::Fact(success)) => Some(success),
            _ => None,
        }
    }

    pub fn factual_success_mut(&mut self) -> Option<&mut VerifiedFactStmtIr> {
        match self {
            StmtResult::Success(VerifiedStmtIr::Fact(success)) => Some(success),
            _ => None,
        }
    }

    pub fn infer_result(&self) -> InferResult {
        if let Some(success) = self.factual_success() {
            success.infers.clone()
        } else if let StmtResult::Success(success) = self {
            success
                .common()
                .map(|common| common.infers.clone())
                .unwrap_or_else(InferResult::new)
        } else {
            InferResult::new()
        }
    }

    pub fn into_factual_success(self) -> Option<VerifiedFactStmtIr> {
        match self {
            StmtResult::Success(VerifiedStmtIr::Fact(success)) => Some(success),
            _ => None,
        }
    }

    pub fn non_factual_ir(&self) -> Option<&VerifiedStmtIr> {
        match self {
            StmtResult::Success(success @ VerifiedStmtIr::UnsafeStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefObjStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefPredicateStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefInterfaceStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefAlgoStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefThmStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::AxiomStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefStrategyStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::By(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Witness(_))
            | StmtResult::Success(success @ VerifiedStmtIr::ProofBlock(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Command(_)) => Some(success),
            StmtResult::Success(VerifiedStmtIr::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }

    pub fn non_factual_ir_mut(&mut self) -> Option<&mut VerifiedStmtIr> {
        match self {
            StmtResult::Success(success @ VerifiedStmtIr::UnsafeStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefObjStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefPredicateStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefInterfaceStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefAlgoStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefThmStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::AxiomStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefStrategyStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::By(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Witness(_))
            | StmtResult::Success(success @ VerifiedStmtIr::ProofBlock(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Command(_)) => Some(success),
            StmtResult::Success(VerifiedStmtIr::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }

    pub fn into_non_factual_ir(self) -> Option<VerifiedStmtIr> {
        match self {
            StmtResult::Success(success @ VerifiedStmtIr::UnsafeStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefObjStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefPredicateStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefInterfaceStmt(_))
            | StmtResult::Success(success @ VerifiedStmtIr::DefAlgoStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefThmStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::AxiomStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::DefStrategyStmt { .. })
            | StmtResult::Success(success @ VerifiedStmtIr::By(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Witness(_))
            | StmtResult::Success(success @ VerifiedStmtIr::ProofBlock(_))
            | StmtResult::Success(success @ VerifiedStmtIr::Command(_)) => Some(success),
            StmtResult::Success(VerifiedStmtIr::Fact(_)) | StmtResult::Unknown(_) => None,
        }
    }
}
