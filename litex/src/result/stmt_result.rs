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

const VERIFIED_BY: &str = "verified by";
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
    fn infer_block(infer_result: &InferResult) -> String {
        if infer_result.infer_facts.is_empty() {
            return String::new();
        }
        format!("\n\n{}\n{}", INFER_COLON, infer_result.infer_facts.join("\n"))
    }

    /// Returns the result body string without any line/file prefix (for tests or when location is not needed).
    pub fn body_string(&self) -> String {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => {
                format!("{}\n{}{}", SUCCESS_COLON, x.stmt, Self::infer_block(&x.infers))
            }
            NonErrStmtExecResult::FactVerifiedByFact(x) => {
                format!("{}\n{}\n{}\n{}{}", SUCCESS_COLON, x.fact, VERIFIED_BY, x.verified_by, Self::infer_block(&x.infers))
            }
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => {
                format!("{}\n{}\n{}\n{}{}", SUCCESS_COLON, x.fact, VERIFIED_BY, x.verified_by, Self::infer_block(&x.infers))
            }
            NonErrStmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }

}

impl NonErrStmtExecResult {
    #[allow(dead_code)]
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