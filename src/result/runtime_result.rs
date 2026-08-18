use crate::prelude::*;

/// The canonical result of executing one Litex statement.
///
/// A successful result owns the verifier evidence needed by downstream
/// consumers. The original `Stmt` already identifies the statement family,
/// so this sum does not repeat every statement variant.
#[derive(Debug)]
pub enum StmtResult {
    Success(VerifiedStmtIr),
    Unknown(UnknownStatementResult),
}

#[derive(Debug)]
pub struct VerifiedStmtIr {
    pub statement: Stmt,
    pub verification: VerifiedStmtVerificationIr,
    pub well_definedness: WellDefinednessCertificate,
}

#[derive(Debug)]
pub enum VerifiedStmtVerificationIr {
    Fact(FactualStmtSuccess),
    NonFact(NonFactualStmtSuccess),
}

#[derive(Debug)]
pub enum UnknownStatementResult {
    Statement(StmtUnknown),
    Fact(FactUnknown),
}

impl From<NonFactualStmtSuccess> for StmtResult {
    fn from(success: NonFactualStmtSuccess) -> Self {
        let statement = success.stmt.clone();
        let well_definedness = success.well_definedness.clone();
        StmtResult::Success(VerifiedStmtIr {
            statement,
            verification: VerifiedStmtVerificationIr::NonFact(success),
            well_definedness,
        })
    }
}

impl From<FactualStmtSuccess> for StmtResult {
    fn from(success: FactualStmtSuccess) -> Self {
        let statement = Stmt::Fact(success.stmt.clone());
        let well_definedness = success.well_definedness.clone();
        StmtResult::Success(VerifiedStmtIr {
            statement,
            verification: VerifiedStmtVerificationIr::Fact(success),
            well_definedness,
        })
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
            success.well_definedness = certificate.clone();
            match &mut success.verification {
                VerifiedStmtVerificationIr::Fact(verification) => {
                    verification.well_definedness = certificate;
                }
                VerifiedStmtVerificationIr::NonFact(verification) => {
                    verification.well_definedness = certificate;
                }
            }
        }
        self
    }

    pub fn fact_id(&self) -> Option<FactId> {
        self.factual_success().and_then(|success| success.fact_id)
    }

    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        if let Some(success) = self.non_factual_success_mut() {
            success.infers.new_infer_result_inside(infer_result);
        } else if let Some(success) = self.factual_success_mut() {
            success.infers.new_infer_result_inside(infer_result);
        }
        self
    }

    pub fn with_execution_trace(mut self, trace: StatementExecutionTrace) -> Self {
        if let Some(success) = self.non_factual_success_mut() {
            success.execution_trace = Some(trace);
        } else if let Some(success) = self.factual_success_mut() {
            success.execution_trace = Some(trace);
        }
        self
    }

    pub fn execution_trace(&self) -> Option<&StatementExecutionTrace> {
        if let Some(success) = self.non_factual_success() {
            success.execution_trace.as_ref()
        } else if let Some(success) = self.factual_success() {
            success.execution_trace.as_ref()
        } else {
            None
        }
    }

    pub fn statement(&self) -> Option<&Stmt> {
        match self {
            StmtResult::Success(success) => Some(&success.statement),
            StmtResult::Unknown(_) => None,
        }
    }

    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        match self {
            StmtResult::Success(success) => success.statement.line_file(),
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

    pub fn factual_success(&self) -> Option<&FactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::Fact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }

    pub fn factual_success_mut(&mut self) -> Option<&mut FactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::Fact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }

    pub fn non_factual_success(&self) -> Option<&NonFactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::NonFact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }

    pub fn non_factual_success_mut(&mut self) -> Option<&mut NonFactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::NonFact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }

    pub fn infer_result(&self) -> InferResult {
        if let Some(success) = self.non_factual_success() {
            success.infers.clone()
        } else if let Some(success) = self.factual_success() {
            success.infers.clone()
        } else {
            InferResult::new()
        }
    }

    pub fn into_factual_success(self) -> Option<FactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::Fact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }

    pub fn into_non_factual_success(self) -> Option<NonFactualStmtSuccess> {
        match self {
            StmtResult::Success(VerifiedStmtIr {
                verification: VerifiedStmtVerificationIr::NonFact(success),
                ..
            }) => Some(success),
            _ => None,
        }
    }
}
