use crate::execute::exec_stmt_result::{
    ExecDefinitionStmtResult, ExecStmtResult,
};
use crate::execute::execute_def_strategy_stmt::{
    ExecDefStrategyStmtFailed, ExecDefStrategyStmtResult,
};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
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

#[test]
fn strategy_executes_proof_statements_and_keeps_helpers_local() {
    let mut runtime = runtime_with_file_env();
    let run = runtime.run_litex_code(include_str!(
        "../../../examples/stmt_nodes/definition/strategy_nested_proof.lit"
    )).unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
        ExecDefStrategyStmtResult::Success(success),
    )) = &run.statement_results[1] else { panic!("strategy did not succeed") };
    assert_eq!(success.proof_steps.len(), 5);
    let detailed = format!("{:?}", crate::json_output::project_stmt_detailed(
        &run.statement_results[1], &runtime,
    ));
    for kind in ["have_obj_equal", "claim", "witness", "obtain_obj_from_exist_fact", "by_def"] {
        assert!(detailed.contains(kind), "{kind}: {detailed}");
    }
    assert_eq!(runtime.execution_environments_stack.len(), 1);
    assert!(!runtime.run_litex_code("helper = 0\n").unwrap().success);
}

#[test]
fn strategy_nested_failure_rolls_back_and_name_can_be_reused() {
    let mut runtime = runtime_with_file_env();
    assert!(runtime.run_litex_code("prop same(x R):\n    x = 0\n").unwrap().success);
    let run = runtime.run_litex_code("strategy use_same:\n    ? forall x R:\n        x = 0\n        =>:\n            $same(x)\n    have helper R = 1\n    claim:\n        ? helper = 0\n        helper = 0\n").unwrap();
    assert!(!run.success);
    assert!(run.session_error.is_none());
    assert!(matches!(&run.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
            ExecDefStrategyStmtResult::Failed(ExecDefStrategyStmtFailed::ProofBody(f))
        )) if f.step_index == 1));
    assert!(runtime.def_strategy_visible_in_stack("use_same").is_none());
    assert_eq!(runtime.execution_environments_stack.len(), 1);
    assert!(runtime.run_litex_code("have helper R = 1\nstrategy use_same:\n    ? forall x R:\n        x = 0\n        =>:\n            $same(x)\n    by def $same(x)\n").unwrap().success);
    assert!(!runtime.run_litex_code("helper = 0\n").unwrap().success);
}

#[test]
fn strategy_goal_wd_precedes_local_definition_and_checks_final_goal() {
    let mut runtime = runtime_with_file_env();
    let run = runtime.run_litex_code("strategy impossible:\n    ? forall x R:\n        $missing(x)\n    prop missing(z R):\n        z = z\n    by def $missing(x)\n").unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(matches!(&run.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
            ExecDefStrategyStmtResult::Failed(ExecDefStrategyStmtFailed::GoalWd(_))
        ))));
    assert!(runtime.def_strategy_visible_in_stack("impossible").is_none());
    assert!(runtime.run_litex_code("prop missing(x R):\n    x = 0\n").unwrap().success);
    let run = runtime.run_litex_code("strategy impossible:\n    ? forall x R:\n        x = 1\n        =>:\n            $missing(x)\n    have helper R = x\n    claim:\n        ? helper = 1\n        helper = 1\n").unwrap();
    assert!(matches!(&run.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
            ExecDefStrategyStmtResult::Failed(ExecDefStrategyStmtFailed::Conclusion { .. })
        ))));
    assert_eq!(runtime.execution_environments_stack.len(), 1);
    assert!(runtime.def_strategy_visible_in_stack("impossible").is_none());
}
