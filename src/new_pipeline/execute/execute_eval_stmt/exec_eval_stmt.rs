use super::helper::evaluate_obj_for_eval_stmt;
use super::result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
use crate::new_pipeline::ast::stmt::EvalStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// eval expr: evaluate a supported closed expression for display.
//
// Condition: `expr` belongs to the closed numeric executable subset
// (exact rational, else closed decimal). No proof fact is stored.
// After: Success carries source + evaluated object; Failed if unsupported.
//
// Example:
//   eval (1 + 2)^2
//   # → evaluated_object = 9
pub fn exec_eval_stmt(
    _runtime: &mut Runtime,
    stmt: &EvalStmt,
) -> RuntimeResult<ExecCommandStmtResult> {
    let Some(evaluated_object) = evaluate_obj_for_eval_stmt(&stmt.obj_to_eval) else {
        return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::UnsupportedExpression,
        )));
    };
    Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
        ExecEvalStmtSuccess {
            statement: stmt.clone(),
            source_object: stmt.obj_to_eval.clone(),
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
            ))) => match success.evaluated_object {
                Obj::Literal(Literal::Number(Number { normalized_value })) => {
                    assert_eq!(normalized_value, "9");
                }
                other => panic!("expected number 9, got {other:?}"),
            },
            other => panic!("expected eval Success, failed={}", other.is_failed()),
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
            other => panic!("expected UnsupportedExpression, failed={}", other.is_failed()),
        }
    }
}
