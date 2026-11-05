use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;
const SOURCE: &str = r#"# Evaluate the empty determinant; its multiplicative identity is one.
eval det(zero_matrix(0,0),0)
det(zero_matrix(0,0),0)=1
"#;

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    run.statement_results
        .iter_mut()
        .filter_map(|s| match s {
            ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
                p,
            ))) => Some(p),
            _ => None,
        })
        .nth(index)
        .unwrap()
}

#[test]
fn empty_determinant_evaluation_replays_original_literal_expansion_without_aggregate() {
    let (mut run, compiler) = super::execute(SOURCE);
    let p = eval(&mut run, 0);
    assert_eq!(p.matrix_scalar_evaluations.len(), 1);
    assert!(p.aggregate_evaluations.is_empty());
    assert!(p.function_evaluations.is_empty());
    let out = compiler
        .compile_run(&run, "empty_determinant_eval")
        .unwrap();
    assert!(out.contains("Litex.matrixDeterminantZero"));
    assert_eq!(
        out,
        compiler
            .compile_run(&run, "empty_determinant_eval")
            .unwrap()
    );
}

#[test]
fn empty_determinant_evaluation_requires_exact_recorded_expansion_value_source_and_wd() {
    for change in ["expansion", "value", "source", "wd", "missing"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = eval(&mut run, 0);
        if change == "missing" {
            p.matrix_scalar_evaluations.clear();
        } else {
            let record = &mut p.matrix_scalar_evaluations[0];
            match change {
                "expansion" => record.expression = super::number_object("0"),
                "value" => record.value = super::number_object("0"),
                "source" => record.source = super::number_object("0"),
                _ => {
                    let DetailedObjWellDefinedProof::ByDef { obj, .. } =
                        record.source_well_defined.as_detailed_mut().unwrap()
                    else {
                        panic!()
                    };
                    *obj = super::number_object("0");
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_empty_det_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn empty_determinant_evaluation_does_not_consume_unrelated_aggregate_records() {
    let source = format!("eval finite_set_product({{}},fn(k Z) C{{0}})\n{SOURCE}");
    let (mut run, compiler) = super::execute(&source);
    let unrelated = std::mem::take(&mut eval(&mut run, 0).aggregate_evaluations);
    assert_eq!(unrelated.len(), 1);
    assert!(eval(&mut run, 1).aggregate_evaluations.is_empty());
    eval(&mut run, 1).aggregate_evaluations = unrelated;
    assert!(compiler
        .compile_run(&run, "unused_empty_det_aggregate")
        .is_err());
}
