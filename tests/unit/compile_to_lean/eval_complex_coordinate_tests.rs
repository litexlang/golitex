use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ComplexOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const COORDINATES: &str =
    include_str!("../../../lean/examples/evaluated_complex_coordinates/statement.lit");
const MODULUS: &str =
    include_str!("../../../lean/examples/evaluated_complex_modulus/statement.lit");
const ARITHMETIC: &str =
    include_str!("../../../lean/examples/evaluated_complex_coordinate_arithmetic/statement.lit");
const PRODUCT: &str =
    include_str!("../../../lean/examples/evaluated_complex_product_coordinate/statement.lit");
const QUOTIENT: &str =
    include_str!("../../../lean/examples/evaluated_complex_quotient_coordinate/statement.lit");

fn eval(run: &mut RunLitexCodeResult) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn complex_coordinate_eval_replays_exact_original_results() {
    for source in [COORDINATES, MODULUS, ARITHMETIC, PRODUCT, QUOTIENT] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "complex_coordinate_eval")
            .expect(source);
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "complex_coordinate_eval")
                .unwrap()
        );
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
    }
}

#[test]
fn complex_coordinate_eval_rejects_wrong_computed_value() {
    for source in ["eval re(3+4*i)", "eval img(3+4*i)", "eval C_abs(3+4*i)"] {
        let (mut run, compiler) = super::execute(source);
        let proof = eval(&mut run);
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        proof.evaluated_object = wrong.clone();
        proof.evaluated_equal_fact.right = wrong;
        compiler
            .compile_run(&run, "wrong_complex_coordinate")
            .expect_err(source);
    }
}

#[test]
fn complex_coordinate_eval_requires_original_child_and_domain() {
    for change in ["child", "membership"] {
        let (mut run, compiler) = super::execute("eval re(3+4*i)");
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ComplexOperator(
                    ComplexOperatorObjWellDefinedProofByDef::RealPart(wd),
                ),
            ..
        } = eval(&mut run)
            .source_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("real part WD")
        };
        if change == "child" {
            wd.child_obj_well_defined.clear();
        } else {
            wd.requirement_fact_verified.clear();
        }
        compiler
            .compile_run(&run, "missing_complex_wd")
            .expect_err(change);
    }
}

#[test]
fn irrational_complex_modulus_replays_exact_root() {
    let (run, compiler) = super::execute("eval C_abs(1+i)");
    let lean = compiler
        .compile_run(&run, "irrational_complex_modulus")
        .expect("exact root");
    assert!(lean.contains("Litex.complexAbsEqSqrtOfNormSq"));
}
