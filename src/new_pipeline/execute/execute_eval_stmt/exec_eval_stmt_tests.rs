use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::execute::execute_eval_stmt::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult,
};
use crate::new_pipeline::execute::ExecStmtResult;
use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::runtime::Runtime;
use crate::new_pipeline::tokenize::Tokenizer;

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

fn assert_eval_number(runtime: &mut Runtime, code: &str, expected: &str) {
    let outcome = exec_one(runtime, code);
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
            success,
        ))) => match success.evaluated_object {
            Obj::Literal(Literal::Number(Number { normalized_value })) => {
                assert_eq!(normalized_value, expected);
            }
            other => panic!("expected number {expected}, got {other:?}"),
        },
        other => panic!("expected eval Success for `{code}`, failed={}", other.is_failed()),
    }
}

#[test]
fn eval_closed_pow_succeeds_with_nine() {
    let mut runtime = runtime_with_file_env();
    assert_eval_number(&mut runtime, "eval (1 + 2)^2", "9");
}

#[test]
fn eval_after_closed_numeric_equal_rewrite() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 10").is_failed());
    let outcome = exec_one(&mut runtime, "eval a + 1");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
            success,
        ))) => {
            assert_eq!(success.cited_equal_fact_ids.len(), 1);
            match success.evaluated_object {
                Obj::Literal(Literal::Number(Number { normalized_value })) => {
                    assert_eq!(normalized_value, "11");
                }
                other => panic!("expected number 11, got {other:?}"),
            }
        }
        other => panic!("expected eval Success after rewrite, failed={}", other.is_failed()),
    }
}

#[test]
fn eval_algo_call_and_nested_arithmetic() {
    let mut runtime = runtime_with_file_env();
    let algo = "algo nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1";
    assert!(!exec_one(&mut runtime, algo).is_failed());
    assert_eval_number(&mut runtime, "eval nonzero_flag(0)", "0");
    assert_eval_number(&mut runtime, "eval nonzero_flag(1)", "1");
    assert_eval_number(&mut runtime, "eval nonzero_flag(0) + 1", "1");
}

#[test]
fn eval_factorial_sqrt_log_closed_numeric_succeed() {
    let mut runtime = runtime_with_file_env();
    assert_eval_number(&mut runtime, "eval 2!", "2");
    assert_eval_number(&mut runtime, "eval 3!", "6");
    assert_eval_number(&mut runtime, "eval sqrt(4)", "2");
    assert_eval_number(&mut runtime, "eval sqrt(0.36)", "0.6");
    assert_eval_number(&mut runtime, "eval log(2, 8)", "3");
}

#[test]
fn eval_non_square_sqrt_soft_fails() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "eval sqrt(2)");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::EvaluationFailed,
        ))) => {}
        other => panic!(
            "expected EvaluationFailed for sqrt(2), failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn eval_standard_set_soft_fails() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "eval N");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::UnsupportedExpression,
        ))) => {}
        other => panic!(
            "expected UnsupportedExpression, failed={}",
            other.is_failed()
        ),
    }
}
