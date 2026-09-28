use crate::execute::exec_stmt_result::{
    ExecDefinitionStmtResult, ExecStmtResult,
};
use crate::execute::execute_def_strategy_stmt::{
    ExecDefStrategyStmtFailed, ExecDefStrategyStmtResult,
};
use crate::launch_command::LaunchCommand;
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
    runtime
        .exec_stmt(&stmts[0])
        .expect("exec_stmt RuntimeResult")
}

#[test]
fn def_strategy_forall_refl_succeeds() {
    let mut runtime = runtime_with_file_env();
    let code = "strategy refl_on_r:\n    ? forall x R:\n        x = x";
    let r = exec_one(&mut runtime, code);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
            ExecDefStrategyStmtResult::Success(_),
        )) => {}
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
            ExecDefStrategyStmtResult::Failed(f),
        )) => {
            let kind = match f {
                ExecDefStrategyStmtFailed::NameClash(msg) => format!("NameClash:{msg}"),
                ExecDefStrategyStmtFailed::GoalWd(_) => "GoalWd".to_string(),
                ExecDefStrategyStmtFailed::Introduce(msg) => format!("Introduce:{msg}"),
                ExecDefStrategyStmtFailed::ProofBody(_) => "ProofBody".to_string(),
                ExecDefStrategyStmtFailed::Conclusion { index, .. } => {
                    format!("Conclusion:{index}")
                }
            };
            panic!("strategy failed: {kind}")
        }
        other => panic!("unexpected result: failed={}", other.is_failed()),
    }
    assert!(runtime.def_strategy_visible_in_stack("refl_on_r").is_some());
}
