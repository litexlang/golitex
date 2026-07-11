use crate::prelude::*;

#[derive(Debug)]
pub enum CommandStmtResult {
    ImportStmt(NonFactualStmtSuccess),
    LocalImportStmt(NonFactualStmtSuccess),
    DoNothingStmt(NonFactualStmtSuccess),
    ClearStmt(NonFactualStmtSuccess),
    EvalStmt(NonFactualStmtSuccess),
    EvalByStmt(NonFactualStmtSuccess),
    UseStrategyStmt(NonFactualStmtSuccess),
    StopStrategyStmt(NonFactualStmtSuccess),
}

impl CommandStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::Command(CommandStmt::ImportStmt(_)) => CommandStmtResult::ImportStmt(success),
            Stmt::Command(CommandStmt::LocalImportStmt(_)) => {
                CommandStmtResult::LocalImportStmt(success)
            }
            Stmt::Command(CommandStmt::DoNothingStmt(_)) => {
                CommandStmtResult::DoNothingStmt(success)
            }
            Stmt::Command(CommandStmt::ClearStmt(_)) => CommandStmtResult::ClearStmt(success),
            Stmt::Command(CommandStmt::EvalStmt(_)) => CommandStmtResult::EvalStmt(success),
            Stmt::Command(CommandStmt::EvalByStmt(_)) => CommandStmtResult::EvalByStmt(success),
            Stmt::Command(CommandStmt::UseStrategyStmt(_)) => {
                CommandStmtResult::UseStrategyStmt(success)
            }
            Stmt::Command(CommandStmt::StopStrategyStmt(_)) => {
                CommandStmtResult::StopStrategyStmt(success)
            }
            _ => panic!("expected command stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            CommandStmtResult::ImportStmt(success)
            | CommandStmtResult::LocalImportStmt(success)
            | CommandStmtResult::DoNothingStmt(success)
            | CommandStmtResult::ClearStmt(success)
            | CommandStmtResult::EvalStmt(success)
            | CommandStmtResult::EvalByStmt(success)
            | CommandStmtResult::UseStrategyStmt(success)
            | CommandStmtResult::StopStrategyStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            CommandStmtResult::ImportStmt(success)
            | CommandStmtResult::LocalImportStmt(success)
            | CommandStmtResult::DoNothingStmt(success)
            | CommandStmtResult::ClearStmt(success)
            | CommandStmtResult::EvalStmt(success)
            | CommandStmtResult::EvalByStmt(success)
            | CommandStmtResult::UseStrategyStmt(success)
            | CommandStmtResult::StopStrategyStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            CommandStmtResult::ImportStmt(success)
            | CommandStmtResult::LocalImportStmt(success)
            | CommandStmtResult::DoNothingStmt(success)
            | CommandStmtResult::ClearStmt(success)
            | CommandStmtResult::EvalStmt(success)
            | CommandStmtResult::EvalByStmt(success)
            | CommandStmtResult::UseStrategyStmt(success)
            | CommandStmtResult::StopStrategyStmt(success) => success,
        }
    }
}
