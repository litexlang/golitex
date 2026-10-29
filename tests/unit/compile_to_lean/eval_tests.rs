use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ArithmeticOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;
use crate::runtime::runtime_ids::FactId;

const ARITHMETIC: &str = include_str!("../../../lean/examples/evaluated_arithmetic/statement.lit");
const CITATIONS: &str =
    include_str!("../../../lean/examples/evaluated_numeric_citations/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/evaluated_local_facts/statement.lit");
const TWO_VALUES: &str = "have a R = 10\nhave b R = 4\neval a * b - b\na * b - b = 36\n";

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("successful eval statement")
    };
    p
}
fn number(s: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(s.to_string())))
}

#[test]
fn eval_replays_exact_arithmetic_citations_and_local_publication() {
    for source in [ARITHMETIC, CITATIONS, LOCAL, TWO_VALUES] {
        let (run, compiler) = super::execute(source);
        let out = compiler.compile_run(&run, "eval_result").expect(source);
        assert!(!out.contains("sorry") && !out.contains("admit"));
    }
}

#[test]
fn eval_rejects_changed_endpoints_and_false_values() {
    for change in ["statement", "source", "left", "right", "rewrite", "value"] {
        let (mut run, compiler) = super::execute("eval 2 + 3\n");
        let p = eval(&mut run, 0);
        match change {
            "statement" => p.statement.obj_to_eval = number("7"),
            "source" => p.source_object = number("7"),
            "left" => p.evaluated_equal_fact.left = number("7"),
            "right" => p.evaluated_equal_fact.right = number("7"),
            "rewrite" => p.rewritten_object = number("7"),
            "value" => {
                p.evaluated_object = number("7");
                p.evaluated_equal_fact.right = number("7");
            }
            _ => unreachable!(),
        }
        let err = compiler.compile_run(&run, "eval_forged").expect_err(change);
        assert!(err.route.starts_with("Eval/"), "{change}: {err:?}");
    }
}

#[test]
fn eval_requires_original_ordered_numeric_citations() {
    for change in ["missing", "wrong_id", "duplicate", "order", "self"] {
        let (mut run, compiler) = super::execute(TWO_VALUES);
        let p = eval(&mut run, 2);
        assert_eq!(p.cited_equal_fact_ids.len(), 2);
        match change {
            "missing" => p.cited_equal_fact_ids.clear(),
            "wrong_id" => p.cited_equal_fact_ids[0] = FactId::new(u64::MAX),
            "duplicate" => p.cited_equal_fact_ids.push(p.cited_equal_fact_ids[0]),
            "order" => p.cited_equal_fact_ids.swap(0, 1),
            "self" => p.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id,
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "eval_citation")
            .expect_err(change);
    }
}

#[test]
fn eval_cannot_use_a_future_producer() {
    let (mut run, compiler) = super::execute(CITATIONS);
    run.statement_results.swap(0, 1);
    compiler
        .compile_run(&run, "eval_future")
        .expect_err("producer follows eval");
}

#[test]
fn eval_cannot_cite_an_equality_from_a_closed_sketch() {
    use crate::execute::execute_proof_block_stmt::{
        ExecProofBlockStmtResult, ExecSketchStmtResult,
    };
    let (mut run, compiler) = super::execute(LOCAL);
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
        ExecSketchStmtResult::Success(sketch),
    )) = &run.statement_results[0]
    else {
        panic!("sketch")
    };
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(local))) =
        &sketch.proof_steps[1]
    else {
        panic!("local eval")
    };
    let local_id = local.evaluated_equal_fact.fact_id;
    eval(&mut run, 2).cited_equal_fact_ids[0] = local_id;
    compiler
        .compile_run(&run, "eval_scope")
        .expect_err("closed local fact");
}

#[test]
fn eval_rejects_a_mismatched_wd_constructor() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AddObjWellDefinedProof;
    let (mut run, compiler) = super::execute("eval 6 / 3\n");
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ArithmeticOperator(proof),
        ..
    } = (&mut eval(&mut run, 0).source_well_defined)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("arithmetic WD")
    };
    let ArithmeticOperatorObjWellDefinedProofByDef::Div(p) = proof else {
        panic!("division")
    };
    *proof = ArithmeticOperatorObjWellDefinedProofByDef::Add(AddObjWellDefinedProof {
        child_obj_well_defined: std::mem::take(&mut p.child_obj_well_defined),
        requirement_fact_verified: std::mem::take(&mut p.requirement_fact_verified),
    });
    let err = compiler
        .compile_run(&run, "eval_wd_tag")
        .expect_err("wrong constructor");
    assert_eq!(err.route, "Eval/WDConstructor");
}

#[test]
fn eval_requires_original_child_wd_and_divisor_guard() {
    for change in ["child", "guard"] {
        let (mut run, compiler) = super::execute("eval 6 / 3\n");
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                ),
            ..
        } = (&mut eval(&mut run, 0).source_well_defined)
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("division WD")
        };
        match change {
            "child" => {
                p.child_obj_well_defined.pop();
            }
            "guard" => p.requirement_fact_verified.clear(),
            _ => unreachable!(),
        }
        compiler.compile_run(&run, "eval_wd").expect_err(change);
    }
}

#[test]
fn eval_checks_the_published_equality_identity_and_subject() {
    for change in ["identity", "subject", "endpoint_wd"] {
        let (mut run, compiler) = super::execute("eval 2 + 3\n");
        let p = eval(&mut run, 0);
        match change {
            "endpoint_wd" => match (&mut p
                .evaluated_equal_well_defined
                .as_detailed_mut()
                .unwrap()
                .right)
                .as_detailed_mut()
                .unwrap()
            {
                DetailedObjWellDefinedProof::ByDef { obj, .. }
                | DetailedObjWellDefinedProof::ByKnown { obj, .. } => *obj = number("7"),
            },
            _ => {
                let StoreFactResult::AtomicFact(store) = &mut p.store_and_infer_result.store else {
                    panic!("atomic store")
                };
                if change == "identity" {
                    store.fact_id = FactId::new(u64::MAX);
                } else {
                    let AtomicFact::EqualFact(eq) = &mut store.fact else {
                        panic!("equality store")
                    };
                    eq.right = number("7");
                }
            }
        }
        compiler.compile_run(&run, "eval_store").expect_err(change);
    }
}

#[test]
fn eval_rejects_an_unsupported_operator_after_a_supported_prefix() {
    let (run, compiler) =
        super::execute("1 = 1\neval (sqrt(2)+sqrt(3))*(sqrt(5)+sqrt(7))*(sqrt(2)+sqrt(3))\n");
    let err = compiler
        .compile_run(&run, "eval_unsupported")
        .expect_err("bounded scalar adapter");
    assert_eq!(err.statement_index, Some(2));
    assert!(err.route.starts_with("WD/") || err.route.starts_with("Eval/"));
}
