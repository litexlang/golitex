use crate::prelude::*;

#[derive(Debug)]
pub enum StmtExecResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactualStmtSuccess(FactualStmtSuccess),
    StmtUnknown(StmtUnknown),
}

const VERIFIED_BY: &str = "verified by";
const INFER_COLON: &str = "infer:";

impl StmtExecResult {
    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        match &mut self {
            StmtExecResult::NonFactualStmtSuccess(x) => {
                x.infers.new_infer_result_inside(infer_result)
            }
            StmtExecResult::FactualStmtSuccess(x) => {
                x.infers.new_infer_result_inside(infer_result)
            }
            StmtExecResult::StmtUnknown(_) => {}
        }
        self
    }
}

impl StmtExecResult {
    fn infer_block_string(infer_result: &InferResult) -> String {
        if infer_result.is_empty() {
            return String::new();
        }
        format!(
            "\n\n{}\n{}",
            INFER_COLON,
            infer_result.join_infer_lines("\n")
        )
    }

    /// Returns the result body string without any line/file prefix (for tests or when location is not needed).
    pub fn body_string(&self) -> String {
        match self {
            StmtExecResult::NonFactualStmtSuccess(x) => {
                format!(
                    "{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    Self::infer_block_string(&x.infers)
                )
            }
            StmtExecResult::FactualStmtSuccess(x) => {
                format!(
                    "{}\n{}\n{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    VERIFIED_BY,
                    x.msg,
                    Self::infer_block_string(&x.infers)
                )
            }
            StmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }
}

impl StmtExecResult {
    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        match self {
            StmtExecResult::NonFactualStmtSuccess(x) => x.stmt.line_file(),
            StmtExecResult::FactualStmtSuccess(x) => x.stmt.line_file(),
            StmtExecResult::StmtUnknown(_) => default_line_file(),
        }
    }
}

impl StmtExecResult {
    pub fn is_true(&self) -> bool {
        match self {
            StmtExecResult::NonFactualStmtSuccess(_) => true,
            StmtExecResult::FactualStmtSuccess(_) => true,
            StmtExecResult::StmtUnknown(_) => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            StmtExecResult::StmtUnknown(_) => true,
            StmtExecResult::NonFactualStmtSuccess(_) => false,
            StmtExecResult::FactualStmtSuccess(_) => false,
        }
    }
}
