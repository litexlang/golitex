use crate::common::keywords::SUCCESS_COLON;
use crate::infer::InferResult;
use super::stmt_success::{FactVerifiedByBuiltinRules, FactVerifiedByFact, NonFactualStmtSuccess};
use super::stmt_unknown::StmtUnknown;

pub enum NonErrStmtExecResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
    StmtUnknown(StmtUnknown),
}

const VERIFIED_BY: &str = "verified by:";
const INFER_COLON: &str = "infer:";

impl NonErrStmtExecResult {
    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        match &mut self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => x.infers.append(infer_result),
            NonErrStmtExecResult::FactVerifiedByFact(x) => x.infers.append(infer_result),
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => x.infers.append(infer_result),
            NonErrStmtExecResult::StmtUnknown(_) => {}
        }
        self
    }
}

impl NonErrStmtExecResult {
    /// Returns the result body string without any line/file prefix (for tests or when location is not needed).
    pub fn body_string(&self) -> String {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => format!("{}\n{}\n{}\n{}", SUCCESS_COLON, x.stmt, INFER_COLON, x.infers.infer_facts.join("\n")),
            NonErrStmtExecResult::FactVerifiedByFact(x) => format!("{}\n{}\n{}\n{}\n{}\n{}", SUCCESS_COLON, x.fact, VERIFIED_BY, x.verified_by, INFER_COLON, x.infers.infer_facts.join("\n")),
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => format!("{}\n{}\n{}\n{}\n{}\n{}", SUCCESS_COLON, x.fact, VERIFIED_BY, x.verified_by, INFER_COLON, x.infers.infer_facts.join("\n")),
            NonErrStmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }

    /// Returns the content part without the "Success:" label (used when displaying with "Success on line N").
    pub fn content_without_success_label(&self) -> String {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => x.stmt.clone(),
            NonErrStmtExecResult::FactVerifiedByFact(x) => format!("{}\n{}\n{}", x.fact, VERIFIED_BY, x.verified_by),
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => format!("{}\n{}\n{}", x.fact, VERIFIED_BY, x.verified_by),
            NonErrStmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }
}

impl NonErrStmtExecResult {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => x.line_file_index,
            NonErrStmtExecResult::FactVerifiedByFact(x) => x.line_file_index,
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => x.line_file_index,
            NonErrStmtExecResult::StmtUnknown(_) => None,
        }
    }
}

impl NonErrStmtExecResult {
    pub fn is_true(&self) -> bool {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(_) => true,
            NonErrStmtExecResult::FactVerifiedByFact(_) => true,
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(_) => true,
            NonErrStmtExecResult::StmtUnknown(_) => false,
        }
    }
}