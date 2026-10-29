use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ExpLogOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/evaluated_square_roots/statement.lit");
const FRACTIONS: &str =
    include_str!("../../../lean/examples/evaluated_fractional_square_roots/statement.lit");
const CITATIONS: &str =
    include_str!("../../../lean/examples/evaluated_cited_square_roots/statement.lit");
const FUNCTIONS: &str =
    include_str!("../../../lean/examples/evaluated_function_square_roots/statement.lit");
const LOCAL: &str =
    include_str!("../../../lean/examples/evaluated_local_square_roots/statement.lit");
const AGGREGATES: &str =
    include_str!("../../../lean/examples/evaluated_square_root_aggregates/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn sqrt_eval_replays_exact_values_citations_functions_and_scope() {
    for source in [SOURCE, FRACTIONS, CITATIONS, FUNCTIONS, LOCAL, AGGREGATES] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "sqrt_eval").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "sqrt_eval").unwrap());
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
    }
}

#[test]
fn sqrt_eval_rejects_wrong_evaluated_result() {
    let (mut run, compiler) = super::execute("eval sqrt(4)");
    let proof = eval(&mut run, 0);
    let wrong = Obj::Literal(Literal::Number(Number::new("3".into())));
    proof.evaluated_object = wrong.clone();
    proof.evaluated_equal_fact.right = wrong;
    compiler
        .compile_run(&run, "wrong_sqrt_value")
        .expect_err("wrong value");
}

#[test]
fn sqrt_eval_requires_original_child_and_nonnegative_proof() {
    for missing in ["child", "nonnegative"] {
        let (mut run, compiler) = super::execute("eval sqrt(4)");
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(
                    wd,
                )),
            ..
        } = eval(&mut run, 0)
            .source_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("sqrt WD")
        };
        if missing == "child" {
            wd.child_obj_well_defined.clear();
        } else {
            wd.requirement_fact_verified.clear();
        }
        compiler
            .compile_run(&run, "missing_sqrt_evidence")
            .expect_err(missing);
    }
}

#[test]
fn sqrt_eval_does_not_replace_original_nonclosed_domain_proofs() {
    let (mut run, compiler) = super::execute(CITATIONS);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(wd)),
        ..
    } = eval(&mut run, 1)
        .source_well_defined
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("sqrt WD")
    };
    assert_eq!(wd.requirement_fact_verified.len(), 2);
    wd.requirement_fact_verified.remove(0);
    compiler
        .compile_run(&run, "missing_real_membership")
        .expect_err("original domain");
}

#[test]
fn sqrt_eval_requires_original_numeric_citation() {
    let (mut run, compiler) = super::execute(CITATIONS);
    let proof = eval(&mut run, 1);
    assert!(!proof.cited_equal_fact_ids.is_empty());
    proof.cited_equal_fact_ids.clear();
    compiler
        .compile_run(&run, "missing_sqrt_citation")
        .expect_err("citation");
}

#[test]
fn sqrt_eval_preserves_negative_and_nonlinear_radical_boundaries() {
    let source = "eval sqrt(-1)";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);

    let (run, compiler) =
        super::execute("eval (sqrt(2)+sqrt(3))*(sqrt(5)+sqrt(7))*(sqrt(2)+sqrt(3))");
    assert_eq!(
        compiler
            .compile_run(&run, "irrational_sqrt")
            .unwrap_err()
            .route,
        "Eval/LinearRadicalDomain"
    );
}
