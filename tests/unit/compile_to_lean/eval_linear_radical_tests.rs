use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ArithmeticOperatorObjWellDefinedProofByDef, ExpLogOperatorObjWellDefinedProofByDef,
};
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const SUM: &str =
    include_str!("../../../lean/examples/evaluated_radical_simplification/statement.lit");

fn eval(run: &mut RunLitexCodeResult) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn exact_linear_radicals_compile() {
    for source in [
        SUM,
        "eval sqrt(8)",
        "eval sqrt(12)-sqrt(3)",
        "eval sqrt(2)+sqrt(2)",
        "eval sqrt(2)*sqrt(3)",
        "eval sqrt(2)*sqrt(2)",
        "eval sqrt(3)*sqrt(6)",
        "eval sqrt(12)*sqrt(27)",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "linear_radical").expect(source);
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
        assert_eq!(lean, compiler.compile_run(&run, "linear_radical").unwrap());
    }
}

#[test]
fn exact_linear_radical_rejects_changed_output_and_citation() {
    for change in ["output", "citation", "wd"] {
        let (mut run, compiler) = super::execute("eval sqrt(8)");
        let proof = eval(&mut run);
        if change == "output" {
            proof.evaluated_object = Obj::Literal(Literal::Number(Number::new("9".into())));
            proof.evaluated_equal_fact.right = proof.evaluated_object.clone();
        } else if change == "citation" {
            proof.cited_equal_fact_ids.push(FactId::new(u64::MAX));
        } else {
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ExpLogOperator(
                        ExpLogOperatorObjWellDefinedProofByDef::Sqrt(wd),
                    ),
                ..
            } = proof.source_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("sqrt WD")
            };
            wd.requirement_fact_verified.clear();
        }
        compiler
            .compile_run(&run, "invalid_linear_radical")
            .expect_err(change);
    }
}

#[test]
fn radical_product_rejects_changed_result_and_citation() {
    for change in ["output", "citation", "wd"] {
        let (mut run, compiler) = super::execute("eval sqrt(2)*sqrt(3)");
        let proof = eval(&mut run);
        if change == "output" {
            proof.evaluated_object = Obj::Literal(Literal::Number(Number::new("9".into())));
            proof.evaluated_equal_fact.right = proof.evaluated_object.clone();
        } else if change == "citation" {
            proof.cited_equal_fact_ids.push(FactId::new(u64::MAX));
        } else {
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ArithmeticOperator(
                        ArithmeticOperatorObjWellDefinedProofByDef::Mul(wd),
                    ),
                ..
            } = proof.source_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("product WD")
            };
            wd.child_obj_well_defined.clear();
        }
        compiler
            .compile_run(&run, "invalid_radical_product")
            .expect_err(change);
    }
}

#[test]
fn cited_radical_replays_original_equality_and_rejects_missing_evidence() {
    let source =
        include_str!("../../../lean/examples/evaluated_cited_irrational_root/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "cited_radical").expect(source);
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &run.statement_results[1]
    else {
        panic!("successful eval")
    };
    assert!(!p.cited_equal_fact_ids.is_empty());
    for id in &p.cited_equal_fact_ids {
        assert!(lean.contains(&format!("h_{}", id.value())));
    }
    for change in ["citation", "output", "wd"] {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
            &mut run.statement_results[1]
        else {
            panic!("successful eval")
        };
        match change {
            "citation" => p.cited_equal_fact_ids.clear(),
            "output" => {
                p.evaluated_object = Obj::Literal(Literal::Number(Number::new("9".into())));
                p.evaluated_equal_fact.right = p.evaluated_object.clone();
            }
            _ => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::ExpLogOperator(
                            ExpLogOperatorObjWellDefinedProofByDef::Sqrt(wd),
                        ),
                    ..
                } = p.source_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!("root WD")
                };
                wd.requirement_fact_verified.clear();
            }
        }
        compiler
            .compile_run(&run, "invalid_cited_radical")
            .expect_err(change);
    }
}
