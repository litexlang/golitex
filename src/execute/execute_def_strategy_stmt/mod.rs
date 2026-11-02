mod exec_def_strategy_local_failure;
mod exec_def_strategy_stmt;

pub use exec_def_strategy_local_failure::{
    ExecDefStrategyEnteredFailed, ExecDefStrategyForallFailed, ExecDefStrategyLocalFailure,
};

#[cfg(test)]
mod exec_def_strategy_stmt_tests;

pub use exec_def_strategy_stmt::{
    exec_def_strategy_stmt, ExecDefStrategyForallProof, ExecDefStrategyStmtFailed,
    ExecDefStrategyStmtResult, ExecDefStrategyStmtSuccess,
};
