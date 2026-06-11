use crate::prelude::*;

#[derive(Debug)]
pub enum StmtResult {
    Unknown(StmtUnknown),
    Fact(Box<FactResult>),
    UnsafeStmt(Box<UnsafeStmtResult>),
    DefObjStmt(Box<DefObjStmtResult>),
    DefPredicateStmt(Box<DefPredicateStmtResult>),
    DefAliasStmt(Box<DefAliasStmtResult>),
    DefInterfaceStmt(Box<DefInterfaceStmtResult>),
    DefAlgoStmt(NonFactualStmtSuccess),
    DefThmStmt(NonFactualStmtSuccess),
    DefStrategyStmt(NonFactualStmtSuccess),
    By(Box<ByStmtResult>),
    Witness(Box<WitnessStmtResult>),
    ProofBlock(Box<ProofBlockStmtResult>),
    Command(Box<CommandStmtResult>),
}

impl From<NonFactualStmtSuccess> for StmtResult {
    fn from(v: NonFactualStmtSuccess) -> Self {
        match &v.stmt {
            Stmt::UnsafeStmt(_) => StmtResult::UnsafeStmt(Box::new(UnsafeStmtResult::new(v))),
            Stmt::DefObjStmt(_) => StmtResult::DefObjStmt(Box::new(DefObjStmtResult::new(v))),
            Stmt::DefPredicateStmt(_) => {
                StmtResult::DefPredicateStmt(Box::new(DefPredicateStmtResult::new(v)))
            }
            Stmt::DefAliasStmt(_) => StmtResult::DefAliasStmt(Box::new(DefAliasStmtResult::new(v))),
            Stmt::DefInterfaceStmt(_) => {
                StmtResult::DefInterfaceStmt(Box::new(DefInterfaceStmtResult::new(v)))
            }
            Stmt::DefAlgoStmt(_) => StmtResult::DefAlgoStmt(v),
            Stmt::DefThmStmt(_) => StmtResult::DefThmStmt(v),
            Stmt::DefStrategyStmt(_) => StmtResult::DefStrategyStmt(v),
            Stmt::By(_) => StmtResult::By(Box::new(ByStmtResult::new(v))),
            Stmt::Witness(_) => StmtResult::Witness(Box::new(WitnessStmtResult::new(v))),
            Stmt::ProofBlock(_) => StmtResult::ProofBlock(Box::new(ProofBlockStmtResult::new(v))),
            Stmt::Command(_) => StmtResult::Command(Box::new(CommandStmtResult::new(v))),
            Stmt::Fact(_) => panic!("fact statement result must be factual"),
        }
    }
}

impl From<FactualStmtSuccess> for StmtResult {
    fn from(v: FactualStmtSuccess) -> Self {
        StmtResult::Fact(Box::new(FactResult::new(v)))
    }
}

impl From<StmtUnknown> for StmtResult {
    fn from(v: StmtUnknown) -> Self {
        StmtResult::Unknown(v)
    }
}

impl From<FactUnknown> for StmtResult {
    fn from(v: FactUnknown) -> Self {
        StmtResult::Fact(Box::new(FactResult::new_unknown(v)))
    }
}

impl StmtResult {
    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        if let Some(x) = self.non_factual_success_mut() {
            x.infers.new_infer_result_inside(infer_result);
        } else if let Some(x) = self.factual_success_mut() {
            x.infers.new_infer_result_inside(infer_result);
        }
        self
    }
}

impl StmtResult {
    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        if let Some(x) = self.non_factual_success() {
            x.stmt.line_file()
        } else if let Some(x) = self.factual_success() {
            x.stmt.line_file()
        } else if let Some(x) = self.as_fact_unknown() {
            x.goal().line_file()
        } else {
            default_line_file()
        }
    }
}

impl StmtResult {
    pub fn is_true(&self) -> bool {
        !self.is_unknown()
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            StmtResult::Unknown(_) => true,
            StmtResult::Fact(x) => x.is_unknown(),
            _ => false,
        }
    }

    pub fn as_unknown(&self) -> Option<&StmtUnknown> {
        match self {
            StmtResult::Unknown(x) => Some(x),
            _ => None,
        }
    }

    pub fn as_fact_unknown(&self) -> Option<&FactUnknown> {
        match self {
            StmtResult::Fact(x) => x.unknown(),
            _ => None,
        }
    }

    pub fn wrap_unknown_for_fact(self, fact: Fact) -> Self {
        match self {
            StmtResult::Unknown(unknown) => FactUnknown::from_stmt_unknown(fact, unknown).into(),
            StmtResult::Fact(fact_result) if fact_result.is_unknown() => {
                StmtResult::Fact(fact_result)
            }
            other => other,
        }
    }

    pub fn factual_success(&self) -> Option<&FactualStmtSuccess> {
        match self {
            StmtResult::Fact(x) => x.success(),
            _ => None,
        }
    }

    pub fn factual_success_mut(&mut self) -> Option<&mut FactualStmtSuccess> {
        match self {
            StmtResult::Fact(x) => x.success_mut(),
            _ => None,
        }
    }

    pub fn non_factual_success(&self) -> Option<&NonFactualStmtSuccess> {
        match self {
            StmtResult::UnsafeStmt(x) => Some(x.success()),
            StmtResult::DefObjStmt(x) => Some(x.success()),
            StmtResult::DefPredicateStmt(x) => Some(x.success()),
            StmtResult::DefAliasStmt(x) => Some(x.success()),
            StmtResult::DefInterfaceStmt(x) => Some(x.success()),
            StmtResult::DefAlgoStmt(x)
            | StmtResult::DefThmStmt(x)
            | StmtResult::DefStrategyStmt(x) => Some(x),
            StmtResult::By(x) => Some(x.success()),
            StmtResult::Witness(x) => Some(x.success()),
            StmtResult::ProofBlock(x) => Some(x.success()),
            StmtResult::Command(x) => Some(x.success()),
            StmtResult::Unknown(_) | StmtResult::Fact(_) => None,
        }
    }

    pub fn non_factual_success_mut(&mut self) -> Option<&mut NonFactualStmtSuccess> {
        match self {
            StmtResult::UnsafeStmt(x) => Some(x.success_mut()),
            StmtResult::DefObjStmt(x) => Some(x.success_mut()),
            StmtResult::DefPredicateStmt(x) => Some(x.success_mut()),
            StmtResult::DefAliasStmt(x) => Some(x.success_mut()),
            StmtResult::DefInterfaceStmt(x) => Some(x.success_mut()),
            StmtResult::DefAlgoStmt(x)
            | StmtResult::DefThmStmt(x)
            | StmtResult::DefStrategyStmt(x) => Some(x),
            StmtResult::By(x) => Some(x.success_mut()),
            StmtResult::Witness(x) => Some(x.success_mut()),
            StmtResult::ProofBlock(x) => Some(x.success_mut()),
            StmtResult::Command(x) => Some(x.success_mut()),
            StmtResult::Unknown(_) | StmtResult::Fact(_) => None,
        }
    }

    pub fn infer_result(&self) -> InferResult {
        if let Some(x) = self.non_factual_success() {
            x.infers.clone()
        } else if let Some(x) = self.factual_success() {
            x.infers.clone()
        } else {
            InferResult::new()
        }
    }

    pub fn into_factual_success(self) -> Option<FactualStmtSuccess> {
        match self {
            StmtResult::Fact(x) => (*x).into_success(),
            _ => None,
        }
    }

    pub fn into_non_factual_success(self) -> Option<NonFactualStmtSuccess> {
        match self {
            StmtResult::UnsafeStmt(x) => Some((*x).into_success()),
            StmtResult::DefObjStmt(x) => Some((*x).into_success()),
            StmtResult::DefPredicateStmt(x) => Some((*x).into_success()),
            StmtResult::DefAliasStmt(x) => Some((*x).into_success()),
            StmtResult::DefInterfaceStmt(x) => Some((*x).into_success()),
            StmtResult::DefAlgoStmt(x)
            | StmtResult::DefThmStmt(x)
            | StmtResult::DefStrategyStmt(x) => Some(x),
            StmtResult::By(x) => Some((*x).into_success()),
            StmtResult::Witness(x) => Some((*x).into_success()),
            StmtResult::ProofBlock(x) => Some((*x).into_success()),
            StmtResult::Command(x) => Some((*x).into_success()),
            StmtResult::Unknown(_) | StmtResult::Fact(_) => None,
        }
    }
}
