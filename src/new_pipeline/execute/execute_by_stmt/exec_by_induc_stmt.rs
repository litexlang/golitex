use super::result::{
    ExecByInducStmtFailed, ExecByInducStmtResult, ExecByStmtResult, ExecByStrongInducStmtFailed,
    ExecByStrongInducStmtResult,
};
use crate::new_pipeline::ast::stmt::{ByInducStmt, ByStrongInducStmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Induction: result types and dispatcher wiring are ready; IH / forall synthesis
// is not fully wired yet, so both paths soft-fail with NotFullyWired.
pub fn exec_by_induc_stmt(
    _runtime: &mut Runtime,
    _stmt: &ByInducStmt,
) -> RuntimeResult<ExecByStmtResult> {
    Ok(ExecByStmtResult::Induc(ExecByInducStmtResult::Failed(
        ExecByInducStmtFailed::NotFullyWired(
            "by induc: induction hypothesis / concluding forall synthesis not fully wired yet"
                .to_string(),
        ),
    )))
}

pub fn exec_by_strong_induc_stmt(
    _runtime: &mut Runtime,
    _stmt: &ByStrongInducStmt,
) -> RuntimeResult<ExecByStmtResult> {
    Ok(ExecByStmtResult::StrongInduc(
        ExecByStrongInducStmtResult::Failed(ExecByStrongInducStmtFailed::NotFullyWired(
            "by strong_induc: strong IH / concluding forall synthesis not fully wired yet"
                .to_string(),
        )),
    ))
}
