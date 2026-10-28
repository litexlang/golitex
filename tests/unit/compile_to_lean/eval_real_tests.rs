use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ArithmeticOperatorObjWellDefinedProofByDef as WD, SignObjWellDefinedProof,
};
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const REAL: &str = include_str!("../../../lean/examples/evaluated_real_operations/statement.lit");
const CITATIONS: &str =
    include_str!("../../../lean/examples/evaluated_real_citations/statement.lit");
const FUNCTIONS: &str =
    include_str!("../../../lean/examples/evaluated_real_functions/statement.lit");
const LOCAL: &str =
    include_str!("../../../lean/examples/evaluated_local_real_operations/statement.lit");
const AGGREGATES: &str =
    include_str!("../../../lean/examples/evaluated_real_aggregates/statement.lit");
const SIGNED: &str =
    include_str!("../../../lean/examples/evaluated_signed_representations/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("eval")
    };
    p
}

#[test]
fn real_eval_replays_exact_values_citations_calls_aggregates_and_local_scope() {
    for source in [REAL, CITATIONS, FUNCTIONS, LOCAL, AGGREGATES, SIGNED] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "real_evaluation").expect(source);
        assert_eq!(
            output,
            compiler.compile_run(&run, "real_evaluation").unwrap()
        );
    }
}

#[test]
fn real_eval_rejects_incorrect_values_for_each_operation() {
    for source in [
        "eval abs(-3)",
        "eval sign(-2)",
        "eval floor(-7/3)",
        "eval ceil(-7/3)",
        "eval min(-1/2,1/3)",
        "eval max(-7,-2)",
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = eval(&mut run, 0);
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        p.evaluated_object = wrong.clone();
        p.evaluated_equal_fact.right = wrong;
        compiler
            .compile_run(&run, "wrong_real_value")
            .expect_err(source);
    }
}

#[test]
fn real_eval_requires_ordered_child_wd_and_matching_constructor() {
    for change in ["missing", "order", "tag"] {
        let source = if change == "tag" {
            "eval abs(-3)"
        } else {
            "eval min(-1/2,1/3)"
        };
        let (mut run, compiler) = super::execute(source);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::ArithmeticOperator(wd),
            ..
        } = (&mut eval(&mut run, 0).source_well_defined)
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("arithmetic WD")
        };
        match wd {
            WD::Min(p) => {
                if change == "missing" {
                    p.child_obj_well_defined.pop();
                } else {
                    p.child_obj_well_defined.swap(0, 1);
                }
            }
            WD::Abs(p) => {
                *wd = WD::Sign(SignObjWellDefinedProof {
                    child_obj_well_defined: std::mem::take(&mut p.child_obj_well_defined),
                    requirement_fact_verified: std::mem::take(&mut p.requirement_fact_verified),
                });
            }
            _ => panic!("source constructor"),
        }
        compiler
            .compile_run(&run, "wrong_real_wd")
            .expect_err(change);
    }
}

#[test]
fn real_eval_keeps_original_rewrite_citations_in_order() {
    for change in ["missing", "order", "self"] {
        let (mut run, compiler) = super::execute(CITATIONS);
        let p = eval(&mut run, 2);
        assert_eq!(p.cited_equal_fact_ids.len(), 2);
        match change {
            "missing" => p.cited_equal_fact_ids.clear(),
            "order" => p.cited_equal_fact_ids.swap(0, 1),
            _ => p.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id,
        }
        compiler
            .compile_run(&run, "wrong_real_citations")
            .expect_err(change);
    }
}

#[test]
fn real_eval_requires_real_membership_for_nonclosed_sources() {
    let (mut run, compiler) = super::execute("have real_arg R = -2\neval floor(real_arg)");
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ArithmeticOperator(WD::Floor(wd)),
        ..
    } = (&mut eval(&mut run, 1).source_well_defined)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("floor WD")
    };
    assert!(!wd.requirement_fact_verified.is_empty());
    wd.requirement_fact_verified.clear();
    compiler
        .compile_run(&run, "missing_real_membership")
        .expect_err("original domain proof");
}

#[test]
fn eval_signed_representation_reuse_requires_the_original_wd_id() {
    let (mut run, compiler) = super::execute("have signed_value R = -7/3\neval signed_value");
    compiler.compile_run(&run, "signed_representation").unwrap();
    let DetailedObjWellDefinedProof::ByKnown { wd_id, .. } = (&mut eval(&mut run, 1)
        .evaluated_equal_well_defined
        .as_detailed_mut()
        .unwrap()
        .right)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("cached negative fraction")
    };
    *wd_id = crate::runtime::runtime_ids::WellDefinednessId::new(u64::MAX);
    compiler
        .compile_run(&run, "wrong_signed_wd")
        .expect_err("original WD identity");
}
