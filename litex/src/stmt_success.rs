use std::fmt;
use crate::keywords::SUCCESS;

pub enum StmtSuccess {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
}

pub struct NonFactualStmtSuccess {
    pub stmt: String,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct FactVerifiedByFact {
    pub fact: String,
    pub verified_by: String,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct FactVerifiedByBuiltinRules {
    pub fact: String,
    pub verified_by: String,
    pub line_file_index: Option<(usize, usize)>,
}

impl fmt::Display for StmtSuccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtSuccess::NonFactualStmtSuccess(non_factual_stmt_success) => write!(f, "{}",  non_factual_stmt_success.to_string()),
            StmtSuccess::FactVerifiedByFact(fact_verified_by_fact) => write!(f, "{}",  fact_verified_by_fact.to_string()),
            StmtSuccess::FactVerifiedByBuiltinRules(fact_verified_by_builtin_rules) => write!(f, "{}\n{}", SUCCESS, fact_verified_by_builtin_rules.to_string()),
        }
    }
}

const VERIFIED_BY: &str = "verified by:";

impl fmt::Display for NonFactualStmtSuccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.stmt)
    }
}

impl fmt::Display for FactVerifiedByFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}\n{}", self.fact, VERIFIED_BY, self.verified_by)
    }
}

impl fmt::Display for FactVerifiedByBuiltinRules {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}\n{}", self.fact, VERIFIED_BY, self.verified_by)
    }
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: String, line_file_index: Option<(usize, usize)>) -> Self {
        NonFactualStmtSuccess { stmt, line_file_index }
    }
}

impl FactVerifiedByFact {
    pub fn new(fact: String, verified_by: String, line_file_index: Option<(usize, usize)>) -> Self {
        FactVerifiedByFact { fact, verified_by, line_file_index }
    }
}

impl FactVerifiedByBuiltinRules {
    pub fn new(fact: String, verified_by: String, line_file_index: Option<(usize, usize)>) -> Self {
        FactVerifiedByBuiltinRules { fact, verified_by, line_file_index }
    }
}
