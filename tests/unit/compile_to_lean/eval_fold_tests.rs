use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualityResult;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const RANGE: &str = include_str!("../../../lean/examples/evaluated_range_folds/statement.lit");
const FINITE: &str = include_str!("../../../lean/examples/evaluated_finite_folds/statement.lit");
const RATIONAL: &str = include_str!("../../../lean/examples/evaluated_rational_fold/statement.lit");
const ARITHMETIC: &str =
    include_str!("../../../lean/examples/evaluated_fold_arithmetic/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/evaluated_local_fold/statement.lit");
const NAMED: &str = include_str!("../../../lean/examples/evaluated_named_fold/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("eval result")
    };
    p
}

#[test]
fn eval_folds_replay_order_seed_empty_rationals_names_and_local_scope() {
    for source in [RANGE, FINITE, RATIONAL, ARITHMETIC, LOCAL, NAMED] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "eval_folds").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "eval_folds").unwrap());
    }
}

#[test]
fn finite_fold_eval_requires_original_commutativity_and_associativity() {
    for change in ["commutative", "associative", "order"] {
        let (mut run, compiler) = super::execute(FINITE);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IteratedOperator(P::FiniteSetReduce(p)),
            ..
        } = &mut eval(&mut run, 0).source_well_defined
        else {
            panic!("finite fold WD")
        };
        match change {
            "commutative" => {
                p.requirement_fact_verified.remove(2);
            }
            "associative" => {
                p.requirement_fact_verified.remove(3);
            }
            _ => p.requirement_fact_verified.swap(2, 3),
        }
        compiler
            .compile_run(&run, "bad_fold_laws")
            .expect_err(change);
    }
}

#[test]
fn eval_folds_reject_missing_reordered_or_other_evaluations() {
    for change in ["missing", "order", "extra", "different"] {
        let (mut run, compiler) = super::execute(ARITHMETIC);
        let p = eval(&mut run, 0);
        assert_eq!(p.aggregate_evaluations.len(), 2);
        match change {
            "missing" => {
                p.aggregate_evaluations.pop();
            }
            "order" => p.aggregate_evaluations.swap(0, 1),
            _ => {
                let (mut other, _) = super::execute(RANGE);
                let record = eval(&mut other, 0).aggregate_evaluations.pop().unwrap();
                if change == "extra" {
                    p.aggregate_evaluations.push(record);
                } else {
                    p.aggregate_evaluations[0] = record;
                }
            }
        }
        compiler
            .compile_run(&run, "bad_fold_evaluations")
            .expect_err(change);
    }
}

#[test]
fn eval_fold_rejects_changed_values_and_missing_constructor_evidence() {
    for source in [RANGE, FINITE] {
        for change in ["value", "child", "signature"] {
            let (mut run, compiler) = super::execute(source);
            let p = eval(&mut run, 0);
            if change == "value" {
                let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
                p.evaluated_object = wrong.clone();
                p.evaluated_equal_fact.right = wrong;
            } else {
                let ObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::IteratedOperator(wd),
                    ..
                } = &mut p.source_well_defined
                else {
                    panic!("fold WD")
                };
                match wd {
                    P::Reduce(w) => {
                        if change == "child" {
                            w.child_obj_well_defined.clear();
                        } else {
                            w.operation_signature_selection = None;
                        }
                    }
                    P::FiniteSetReduce(w) => {
                        if change == "child" {
                            w.child_obj_well_defined.clear();
                        } else {
                            w.operation_signature_selection = None;
                        }
                    }
                    _ => panic!("fold kind"),
                }
            }
            compiler
                .compile_run(&run, "bad_fold_evidence")
                .expect_err(change);
        }
    }
}

#[test]
fn fold_bound_names_reject_changed_operation_bodies() {
    let source = include_str!("../../../lean/examples/fold_bound_names/statement.lit");
    let (mut run, compiler) = super::execute(source);
    compiler.compile_run(&run, "fold_bound_names").unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!("fact")
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!("success")
    };
    let Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(fold)) = &mut p.fact.right else {
        panic!("finite fold")
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = fold.op.as_mut() else {
        panic!("operation")
    };
    f.equal_to = Box::new(Obj::Literal(Literal::Number(Number::new("99".into()))));
    compiler
        .compile_run(&run, "changed_fold_operation")
        .expect_err("operation changed");
}

#[test]
fn eval_alone_declares_its_function_semantics_dependency() {
    for source in [
        "eval reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a-b},0)",
        "eval finite_set_reduce({3,1,2},fn(k Z) Z{k},fn(a,b Z) Z{a+b},10)",
        "eval sum(1,3,fn(k Z) Z{k})",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "standalone_eval").unwrap();
        assert!(lean.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
        assert!(!lean.contains("variable [_setSemantics"));
    }
}
