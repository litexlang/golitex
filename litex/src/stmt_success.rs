use std::fmt;
use crate::stmt::Stmt;
use crate::fact::Fact;
use crate::consts::SUCCESS_COLON;

pub enum StmtSuccess<'a> {
    NonFactualStmtSuccess(NonFactualStmtSuccess<'a>),
    FactVerifiedByFact(FactVerifiedByFact<'a>),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules<'a>),
}

pub struct NonFactualStmtSuccess<'a> {
    pub stmt: &'a Stmt,
}

pub struct FactVerifiedByFact<'a> {
    pub fact: &'a Fact,
    pub verified_by: &'a Fact,
}

pub struct FactVerifiedByBuiltinRules<'a> {
    pub fact: &'a Fact,
    pub verified_by: String,
}

impl<'a> fmt::Display for StmtSuccess<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtSuccess::NonFactualStmtSuccess(non_factual_stmt_success) => write!(f, "{}\n{}", SUCCESS_COLON, non_factual_stmt_success.to_string()),
            StmtSuccess::FactVerifiedByFact(fact_verified_by_fact) => write!(f, "{}\n{}", SUCCESS_COLON, fact_verified_by_fact.to_string()),
            StmtSuccess::FactVerifiedByBuiltinRules(fact_verified_by_builtin_rules) => write!(f, "{}\n{}", SUCCESS_COLON, fact_verified_by_builtin_rules.to_string()),
        }
    }
}

const VERIFIED_BY: &str = "verified by:";

impl<'a> fmt::Display for NonFactualStmtSuccess<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", SUCCESS_COLON, self.stmt)
    }
}

impl<'a> fmt::Display for FactVerifiedByFact<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}\n{}\n{}", SUCCESS_COLON, self.fact, VERIFIED_BY, self.verified_by)
    }
}

impl<'a> fmt::Display for FactVerifiedByBuiltinRules<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}\n{}\n{}", SUCCESS_COLON, self.fact, VERIFIED_BY, self.verified_by)
    }
}

impl<'a> NonFactualStmtSuccess<'a> {
    pub fn new(stmt: &'a Stmt) -> Self {
        NonFactualStmtSuccess { stmt }
    }
}

impl<'a> FactVerifiedByFact<'a> {
    pub fn new(fact: &'a Fact, verified_by: &'a Fact) -> Self {
        FactVerifiedByFact { fact, verified_by }
    }
}

impl<'a> FactVerifiedByBuiltinRules<'a> {
    pub fn new(fact: &'a Fact, verified_by: String) -> Self {
        FactVerifiedByBuiltinRules { fact, verified_by }
    }
}
