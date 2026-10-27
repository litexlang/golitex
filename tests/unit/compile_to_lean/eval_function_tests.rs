use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;
use crate::runtime::runtime_ids::FactId;

const CALLS: &str = include_str!("../../../lean/examples/evaluated_formula_calls/statement.lit");
const CAPTURED: &str =
    include_str!("../../../lean/examples/evaluated_captured_values/statement.lit");
const NESTED: &str = include_str!("../../../lean/examples/evaluated_nested_calls/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/evaluated_local_calls/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("eval")
    };
    p
}
fn number(n: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.into())))
}

#[test]
fn eval_function_examples_replay_original_calls() {
    for source in [CALLS, CAPTURED, NESTED, LOCAL] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "eval_calls").expect(source);
    }
}

#[test]
fn eval_function_result_retains_body_rewrite_and_exact_citations() {
    let (mut run, _) = super::execute(CAPTURED);
    let p = eval(&mut run, 2);
    assert_eq!(p.function_evaluations.len(), 1);
    let f = &p.function_evaluations[0];
    assert_ne!(f.expansion.expanded_body().ir(), f.rewritten_body.ir());
    assert_eq!(f.cited_equal_fact_ids, p.cited_equal_fact_ids);
    assert_eq!(f.cited_equal_fact_ids.len(), 1);
    assert_eq!(f.nested_function_evidence, 0..0);
    assert_eq!(f.value, number("12"));
}

#[test]
fn eval_function_rejects_missing_changed_or_extra_calls() {
    for change in [
        "missing",
        "application",
        "value",
        "expanded",
        "rewritten",
        "extra",
    ] {
        let (mut run, compiler) = super::execute(CALLS);
        if change == "extra" || change == "expanded" {
            let extra = eval(&mut run, 4).function_evaluations.pop().unwrap();
            if change == "extra" {
                eval(&mut run, 1).function_evaluations.push(extra);
            } else {
                eval(&mut run, 1).function_evaluations[0].expansion = extra.expansion;
            }
        } else {
            let p = eval(&mut run, 1);
            match change {
                "missing" => p.function_evaluations.clear(),
                "application" => p.function_evaluations[0].application = number("7"),
                "value" => p.function_evaluations[0].value = number("7"),
                "rewritten" => p.function_evaluations[0].rewritten_body = number("7"),
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "eval_bad_call")
            .expect_err(change);
    }
}

#[test]
fn eval_function_rejects_changed_body_citations_and_flat_capture() {
    for change in [
        "body_missing",
        "flat_missing",
        "wrong_id",
        "self",
        "duplicate",
    ] {
        let (mut run, compiler) = super::execute(CAPTURED);
        let p = eval(&mut run, 2);
        let f = &mut p.function_evaluations[0];
        match change {
            "body_missing" => f.cited_equal_fact_ids.clear(),
            "flat_missing" => p.cited_equal_fact_ids.clear(),
            "wrong_id" => {
                f.cited_equal_fact_ids[0] = FactId::new(u64::MAX);
                p.cited_equal_fact_ids[0] = FactId::new(u64::MAX);
            }
            "self" => {
                f.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id;
                p.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id;
            }
            "duplicate" => {
                f.cited_equal_fact_ids.push(f.cited_equal_fact_ids[0]);
                p.cited_equal_fact_ids.push(p.cited_equal_fact_ids[0]);
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "eval_bad_cites")
            .expect_err(change);
    }
}

#[test]
fn eval_function_cannot_use_a_future_definition() {
    let (mut run, compiler) = super::execute(CALLS);
    run.statement_results.swap(0, 1);
    compiler
        .compile_run(&run, "eval_future_function")
        .expect_err("future definition");
}

#[test]
fn eval_function_rejects_changed_wd_subject() {
    let (mut run, compiler) = super::execute(CALLS);
    match &mut eval(&mut run, 4).function_evaluations[0].application_well_defined {
        ObjWellDefinedProof::ByDef { obj, .. } | ObjWellDefinedProof::ByKnown { obj, .. } => {
            *obj = number("3")
        }
    }
    compiler
        .compile_run(&run, "eval_bad_wd")
        .expect_err("wrong checked call");
}

#[test]
fn eval_nested_function_ranges_preserve_completed_child_order() {
    let (mut run, _) = super::execute(
        "have fn inner(x R) R = x + 1\nhave fn outer(x R) R = inner(x) + inner(x)\neval outer(2)\n",
    );
    let p = eval(&mut run, 2);
    assert_eq!(p.function_evaluations.len(), 3);
    assert_eq!(p.function_evaluations[0].nested_function_evidence, 0..0);
    assert_eq!(p.function_evaluations[1].nested_function_evidence, 1..1);
    assert_eq!(p.function_evaluations[2].nested_function_evidence, 0..2);
}

#[test]
fn eval_function_rejects_invalid_nested_ranges_and_reordered_calls() {
    let source = "have fn inner(x R) R = x + 1\nhave fn outer(x R) R = inner(x) + inner(x+1)\neval outer(2)\n";
    for change in ["start", "end", "order"] {
        let (mut run, compiler) = super::execute(source);
        let p = eval(&mut run, 2);
        assert_eq!(p.function_evaluations.len(), 3);
        match change {
            "start" => p.function_evaluations[2].nested_function_evidence.start = 1,
            "end" => p.function_evaluations[2].nested_function_evidence.end = 3,
            "order" => p.function_evaluations.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "eval_bad_order")
            .expect_err(change);
    }
}
