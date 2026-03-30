use crate::prelude::*;

#[derive(Debug)]
pub enum NonErrStmtExecResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactualStmtSuccess(FactualStmtSuccess),
    StmtUnknown(StmtUnknown),
}

const VERIFIED_BY: &str = "verified by";
const INFER_COLON: &str = "infer:";

impl NonErrStmtExecResult {
    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        match &mut self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => {
                x.infers.new_infer_result_inside(infer_result)
            }
            NonErrStmtExecResult::FactualStmtSuccess(x) => {
                x.infers.new_infer_result_inside(infer_result)
            }
            NonErrStmtExecResult::StmtUnknown(_) => {}
        }
        self
    }
}

impl NonErrStmtExecResult {
    fn infer_block_string(infer_result: &InferResult) -> String {
        if infer_result.infer_facts.is_empty() {
            return String::new();
        }
        format!(
            "\n\n{}\n{}",
            INFER_COLON,
            infer_result.infer_facts.join("\n")
        )
    }

    /// Returns the result body string without any line/file prefix (for tests or when location is not needed).
    pub fn body_string(&self) -> String {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => {
                format!(
                    "{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    Self::infer_block_string(&x.infers)
                )
            }
            NonErrStmtExecResult::FactualStmtSuccess(x) => {
                format!(
                    "{}\n{}\n{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    VERIFIED_BY,
                    x.msg,
                    Self::infer_block_string(&x.infers)
                )
            }
            NonErrStmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }
}

impl NonErrStmtExecResult {
    #[allow(dead_code)]
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => x.stmt.line_file(),
            NonErrStmtExecResult::FactualStmtSuccess(x) => x.stmt.line_file(),
            NonErrStmtExecResult::StmtUnknown(_) => DEFAULT_LINE_FILE,
        }
    }
}

impl NonErrStmtExecResult {
    pub fn is_true(&self) -> bool {
        match self {
            NonErrStmtExecResult::NonFactualStmtSuccess(_) => true,
            NonErrStmtExecResult::FactualStmtSuccess(_) => true,
            NonErrStmtExecResult::StmtUnknown(_) => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            NonErrStmtExecResult::StmtUnknown(_) => true,
            NonErrStmtExecResult::NonFactualStmtSuccess(_) => false,
            NonErrStmtExecResult::FactualStmtSuccess(_) => false,
        }
    }
}
