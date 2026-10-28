use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ExpLogOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const ROOT: &str = include_str!("../../../lean/examples/evaluated_exact_square_root/statement.lit");
const SUM: &str = include_str!("../../../lean/examples/evaluated_exact_radical_sum/statement.lit");
const THREE: &str =
    include_str!("../../../lean/examples/evaluated_exact_radical_sum_three/statement.lit");

fn eval(run: &mut RunLitexCodeResult) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn unchanged_radical_evaluation_replays_exact_original_result() {
    for source in [ROOT, SUM, THREE] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "unchanged_radical")
            .expect(source);
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "unchanged_radical").unwrap()
        );
    }
}

#[test]
fn unchanged_radical_eval_rejects_wrong_output_missing_wd_and_citation() {
    for change in ["output", "wd", "citation"] {
        let (mut run, compiler) = super::execute(ROOT);
        let proof = eval(&mut run);
        match change {
            "output" => {
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
            _ => proof.cited_equal_fact_ids.push(FactId::new(u64::MAX)),
        }
        compiler
            .compile_run(&run, "invalid_unchanged_radical")
            .expect_err(change);
    }
}

#[test]
fn product_of_radical_sums_remains_unsupported() {
    let (run, compiler) = super::execute("eval (sqrt(2)+sqrt(3))*(sqrt(5)+sqrt(7))");
    compiler
        .compile_run(&run, "nonlinear_radical")
        .expect_err("product of radical sums");
}
