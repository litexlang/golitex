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
