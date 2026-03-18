use crate::infer::InferResult;

pub struct NonFactualStmtSuccess {
    pub stmt: String,
    pub infers: InferResult,
    pub line_file_index: (usize, usize),
}

pub struct FactVerifiedByFact {
    pub fact: String,
    pub verified_by: String,
    pub infers: InferResult,
    pub line_file_index: (usize, usize),
    pub verified_by_line_file: (usize, usize),
}

pub struct FactVerifiedByBuiltinRules {
    pub fact: String,
    pub verified_by: String,
    pub infers: InferResult,
    pub line_file_index: (usize, usize),
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: String, infers: InferResult, line_file_index: (usize, usize)) -> Self {
        NonFactualStmtSuccess {
            stmt,
            infers,
            line_file_index,
        }
    }
}

impl FactVerifiedByFact {
    pub fn new(fact: String, verified_by: String, infers: InferResult, line_file_index: (usize, usize), verified_by_line_file: (usize, usize)) -> Self {
        FactVerifiedByFact { fact, verified_by, infers, line_file_index, verified_by_line_file }
    }
}

impl FactVerifiedByBuiltinRules {
    pub fn new(fact: String, verified_by: String, infers: InferResult, line_file_index: (usize, usize)) -> Self {
        FactVerifiedByBuiltinRules { fact, verified_by, infers, line_file_index }
    }
}