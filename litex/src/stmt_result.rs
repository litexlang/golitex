pub enum StmtResult {
    StmtSuccess(StmtSuccess),
    StmtUnknown(StmtUnknown),
    StmtError(StmtError),
}

pub enum StmtSuccess {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
}

pub struct StmtUnknown {
    pub fact: Fact,
}

pub enum StmtError {
    
}