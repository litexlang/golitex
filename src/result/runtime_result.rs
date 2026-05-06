use crate::prelude::*;

#[derive(Debug)]
pub enum StmtResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactualStmtSuccess(FactualStmtSuccess),
    StmtUnknown(StmtUnknown),
}

impl From<NonFactualStmtSuccess> for StmtResult {
    fn from(v: NonFactualStmtSuccess) -> Self {
        StmtResult::NonFactualStmtSuccess(v)
    }
}

impl From<FactualStmtSuccess> for StmtResult {
    fn from(v: FactualStmtSuccess) -> Self {
        StmtResult::FactualStmtSuccess(v)
    }
}

impl From<StmtUnknown> for StmtResult {
    fn from(v: StmtUnknown) -> Self {
        StmtResult::StmtUnknown(v)
    }
}

const VERIFIED_BY: &str = "verified by";
const INFER_COLON: &str = "infer:";

impl StmtResult {
    pub fn with_infers(mut self, infer_result: InferResult) -> Self {
        match &mut self {
            StmtResult::NonFactualStmtSuccess(x) => x.infers.new_infer_result_inside(infer_result),
            StmtResult::FactualStmtSuccess(x) => x.infers.new_infer_result_inside(infer_result),
            StmtResult::StmtUnknown(_) => {}
        }
        self
    }
}

impl StmtResult {
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
            StmtResult::NonFactualStmtSuccess(x) => {
                format!(
                    "{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    Self::infer_block_string(&x.infers)
                )
            }
            StmtResult::FactualStmtSuccess(x) => {
                format!(
                    "{}\n{}\n{}\n{}{}",
                    SUCCESS_COLON,
                    x.stmt,
                    VERIFIED_BY,
                    x.verification_display_line(),
                    Self::infer_block_string(&x.infers)
                )
            }
            StmtResult::StmtUnknown(x) => x.to_string(),
        }
    }
}

impl StmtResult {
    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        match self {
            StmtResult::NonFactualStmtSuccess(x) => x.stmt.line_file(),
            StmtResult::FactualStmtSuccess(x) => x.stmt.line_file(),
            StmtResult::StmtUnknown(_) => default_line_file(),
        }
    }
}

impl StmtResult {
    pub fn is_true(&self) -> bool {
        match self {
            StmtResult::NonFactualStmtSuccess(_) => true,
            StmtResult::FactualStmtSuccess(_) => true,
            StmtResult::StmtUnknown(_) => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            StmtResult::StmtUnknown(_) => true,
            StmtResult::NonFactualStmtSuccess(_) => false,
            StmtResult::FactualStmtSuccess(_) => false,
        }
    }
}
