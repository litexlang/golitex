use crate::fact::Fact;
use crate::infer::InferResult;
use crate::result::NonErrStmtExecResult;
use crate::stmt::Stmt;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<NonErrStmtExecResult>,
}

#[derive(Debug)]
pub struct FactVerifiedByFact {
    pub fact: Fact,
    pub verified_by: String,
    pub infers: InferResult,
    pub verified_by_line_file: (usize, usize),
}

#[derive(Debug)]
pub struct FactVerifiedByBuiltinRules {
    pub fact: Fact,
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
            fact,
            verified_by,
            infers,
            verified_by_line_file,
        }
    }
}

impl FactVerifiedByBuiltinRules {
    pub fn new(fact: Fact, verified_by: String, infers: InferResult) -> Self {
        FactVerifiedByBuiltinRules {
            fact,
            verified_by,
            infers,
        }
    }
}
