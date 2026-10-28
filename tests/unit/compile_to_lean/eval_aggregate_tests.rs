use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const RANGE: &str = include_str!("../../../lean/examples/evaluated_range_aggregates/statement.lit");
const FINITE: &str =
    include_str!("../../../lean/examples/evaluated_finite_aggregates/statement.lit");
const MIXED: &str =
    include_str!("../../../lean/examples/evaluated_aggregate_arithmetic/statement.lit");
const CALLS: &str = include_str!("../../../lean/examples/evaluated_aggregate_calls/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/evaluated_local_aggregates/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("eval result")
    };
    p
}

#[test]
fn eval_aggregates_replay_range_finite_arithmetic_and_local_results() {
    for source in [RANGE, FINITE, MIXED, LOCAL, CALLS] {
        let (run, compiler) = super::execute(source);
        let generated = compiler.compile_run(&run, "eval_aggregates").expect(source);
        assert_eq!(
            generated,
            compiler.compile_run(&run, "eval_aggregates").unwrap()
        );
    }
}

#[test]
fn eval_aggregate_rejects_missing_extra_wrong_or_reordered_records() {
    for change in ["missing", "extra", "wrong", "reordered"] {
        let (mut run, compiler) = super::execute(MIXED);
        let p = eval(&mut run, 0);
        assert_eq!(p.aggregate_evaluations.len(), 2);
        match change {
            "missing" => {
                p.aggregate_evaluations.pop();
            }
            "extra" | "wrong" => {
                let (mut other, _) = super::execute("eval sum(1,2,fn(x Z) Z {x})");
                let record = eval(&mut other, 0).aggregate_evaluations.pop().unwrap();
                if change == "extra" {
                    p.aggregate_evaluations.push(record);
                } else {
                    p.aggregate_evaluations[0] = record;
                }
            }
            _ => p.aggregate_evaluations.swap(0, 1),
        }
        compiler
            .compile_run(&run, "bad_aggregate_record")
            .expect_err(change);
    }
}

#[test]
fn eval_aggregate_rejects_changed_endpoint_or_source_wd() {
    for change in ["value", "wd", "rewritten"] {
        let (mut run, compiler) = super::execute(RANGE);
        let p = eval(&mut run, 0);
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        match change {
            "value" => {
                p.evaluated_object = wrong.clone();
                p.evaluated_equal_fact.right = wrong;
            }
            "rewritten" => p.rewritten_object = wrong,
            _ => match (&mut p.source_well_defined).as_detailed_mut().unwrap() {
                DetailedObjWellDefinedProof::ByDef { obj, .. }
                | DetailedObjWellDefinedProof::ByKnown { obj, .. } => *obj = wrong,
            },
        }
        compiler
            .compile_run(&run, "bad_aggregate_endpoint")
            .expect_err(change);
    }
}

#[test]
fn eval_aggregates_keep_nested_term_body_boundary_explicit() {
    let source = "eval sum(1, 2, fn(x Z) Z {sum(1, 2, fn(y Z) Z {x + y})})";
    let (run, compiler) = super::execute(source);
    compiler
        .compile_run(&run, "nested_aggregate_body")
        .expect_err("nested aggregate term body");
}

#[test]
fn aggregate_calculation_replays_both_sides_and_arithmetic() {
    for source in [
        "sum(1,3,fn(x Z) Z {x}) = product(1,3,fn(x Z) Z {x})",
        "sum(1,4,fn(x Z) Z {x}) + product(1,4,fn(x Z) Z {x}) = 34",
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "aggregate_both_sides")
            .expect(source);
    }
}
