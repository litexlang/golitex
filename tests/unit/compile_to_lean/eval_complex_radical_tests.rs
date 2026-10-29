use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ComplexOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const TWO: &str =
    include_str!("../../../lean/examples/evaluated_irrational_complex_modulus/statement.lit");
const FIVE: &str =
    include_str!("../../../lean/examples/evaluated_irrational_complex_modulus_five/statement.lit");

fn eval(run: &mut RunLitexCodeResult) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn complex_modulus_eval_preserves_exact_irrational_result() {
    for source in [TWO, FIVE] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "complex_modulus_radical")
            .expect(source);
        assert!(lean.contains("Litex.complexAbsEqSqrtOfNormSq"));
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "complex_modulus_radical")
                .unwrap()
        );
    }
}

#[test]
fn complex_modulus_eval_rejects_wrong_root_or_missing_source_wd() {
    for change in ["root", "wd", "citation"] {
        let (mut run, compiler) = super::execute(TWO);
        let proof = eval(&mut run);
        match change {
            "root" => {
                let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = &mut proof.evaluated_object
                else {
                    panic!("sqrt result")
                };
                root.arg = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
                proof.evaluated_equal_fact.right = proof.evaluated_object.clone();
            }
            "wd" => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::ComplexOperator(
                            ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(wd),
                        ),
                    ..
                } = proof.source_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!("complex modulus WD")
                };
                wd.requirement_fact_verified.clear();
            }
            _ => proof.cited_equal_fact_ids.push(FactId::new(u64::MAX)),
        }
        compiler
            .compile_run(&run, "invalid_complex_modulus")
            .expect_err(change);
    }
}

#[test]
fn general_radical_arithmetic_remains_an_explicit_boundary() {
    let (run, compiler) =
        super::execute("eval (sqrt(2)+sqrt(3))*(sqrt(5)+sqrt(7))*(sqrt(2)+sqrt(3))");
    compiler
        .compile_run(&run, "unsupported_radical_product")
        .expect_err("nonlinear radical product");
}
