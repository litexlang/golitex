use crate::prelude::*;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<NonErrStmtExecResult>,
}

pub struct _FactualStmtSuccess {
    pub stmt: Fact,
    pub infers: InferResult,
    pub msg: String,
    pub verified_by_fact: Fact,
    pub inside_results: Vec<NonErrStmtExecResult>,
}

#[derive(Debug)]
pub struct FactVerifiedByFact {
    pub stmt: Fact,
    pub verified_by: String,
    pub infers: InferResult,
    pub verified_by_line_file: (usize, usize),
}

#[derive(Debug)]
pub struct FactVerifiedByBuiltinRules {
    pub stmt: Fact,
    pub verified_by: String,
    pub infers: InferResult,
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: Stmt, infers: InferResult, inside_results: Vec<NonErrStmtExecResult>) -> Self {
        NonFactualStmtSuccess {
            stmt,
            infers,
            inside_results,
        }
    }
}

impl FactVerifiedByFact {
    pub fn new(
        fact: Fact,
        verified_by: String,
        infers: InferResult,
        verified_by_line_file: (usize, usize),
    ) -> Self {
        FactVerifiedByFact {
            stmt: fact,
            verified_by,
            infers,
            verified_by_line_file,
        }
    }
}

impl FactVerifiedByBuiltinRules {
    pub fn new(fact: Fact, verified_by: String, infers: InferResult) -> Self {
        FactVerifiedByBuiltinRules {
            stmt: fact,
            verified_by,
            infers,
        }
    }
}
