use super::helper::evaluate_closed_numeric_obj;
use super::result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
use crate::new_pipeline::ast::stmt::EvalStmt;
use crate::new_pipeline::rational_expression::ClosedNumericExpr;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// eval expr: closed-numeric display evaluation (no proof fact stored).
//
// Stages:
//   1. Substitute known_closed_numeric_equal representatives (atomic-fact rewrite).
//   2. Residual must be ClosedNumericExpr; else soft Failed.
//   3. Simplify (exact rational, else closed decimal).
//
// Example:
//   have a R = 10
//   eval a + 1
//   # → rewritten 10 + 1 → evaluated 11
pub fn exec_eval_stmt(
    runtime: &mut Runtime,
    stmt: &EvalStmt,
) -> RuntimeResult<ExecCommandStmtResult> {
    let (rewritten_object, cited_equal_fact_ids) =
        runtime.rewrite_obj_by_known_closed_numeric_equal(&stmt.obj_to_eval);

    if ClosedNumericExpr::try_from_obj(&rewritten_object).is_none() {
        return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::NotClosedNumericAfterRewrite,
        )));
    }

    let Some(evaluated_object) = evaluate_closed_numeric_obj(&rewritten_object) else {
        return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::EvaluationFailed,
        )));
    };

    Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
        ExecEvalStmtSuccess {
            statement: stmt.clone(),
            source_object: stmt.obj_to_eval.clone(),
            rewritten_object,
            cited_equal_fact_ids,
            evaluated_object,
        },
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
    use crate::new_pipeline::execute::ExecStmtResult;
    use crate::new_pipeline::launch_command::LaunchCommand;
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

    #[test]
    fn eval_closed_pow_succeeds_with_nine() {
        let mut runtime = runtime_with_file_env();
        let outcome = exec_one(&mut runtime, "eval (1 + 2)^2");
        match outcome {
            ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
                success,
            ))) => {
                assert!(success.cited_equal_fact_ids.is_empty());
                match success.evaluated_object {
                    Obj::Literal(Literal::Number(Number { normalized_value })) => {
                        assert_eq!(normalized_value, "9");
                    }
                    other => panic!("expected number 9, got {other:?}"),
                }
            }
            other => panic!("expected eval Success, failed={}", other.is_failed()),
        }
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
    fn eval_factorial_not_closed_numeric_soft_fails() {
        let mut runtime = runtime_with_file_env();
        let outcome = exec_one(&mut runtime, "eval 2!");
        match outcome {
            ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
                ExecEvalStmtFailed::NotClosedNumericAfterRewrite,
            ))) => {}
            other => panic!(
                "expected NotClosedNumericAfterRewrite, failed={}",
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
                ExecEvalStmtFailed::NotClosedNumericAfterRewrite,
            ))) => {}
            other => panic!(
                "expected NotClosedNumericAfterRewrite, failed={}",
                other.is_failed()
            ),
        }
    }
}
