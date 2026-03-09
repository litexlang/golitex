use std::fmt;

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

const VERIFIED_BY: &str = "verified by:";

impl fmt::Display for NonFactualStmtSuccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        _ = self.line_file_index;
        write!(f, "{}", self.stmt)
    }
}

impl fmt::Display for FactVerifiedByFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        _ = self.line_file_index;
        write!(f, "{}\n{}\n{}", self.fact, VERIFIED_BY, self.verified_by)
    }
}

impl fmt::Display for FactVerifiedByBuiltinRules {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        _ = self.line_file_index;
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