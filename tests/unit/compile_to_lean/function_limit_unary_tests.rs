use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const NEG: &str =
    include_str!("../../../lean/examples/function_limit_at_neg_by_theorem/statement.lit");

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut p.proof_steps[0]
    else {
        panic!("unary limit invocation")
    };
    p
}

#[test]
fn unary_limit_algebra_replays_all_five_approaches() {
    for source in [
        NEG,
        include_str!("../../../lean/examples/function_limit_at_abs_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_neg_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_abs_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_neg_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_abs_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_inf_neg_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_inf_abs_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_inf_neg_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_inf_abs_by_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "unary_limit")
            .unwrap()
            .contains("FunctionLimitMap"));
    }
}

#[test]
fn unary_limit_algebra_requires_original_ordered_premises() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(NEG);
        let p = invocation(&mut run);
        match mutation {
            0 => {
                p.dom_proofs.pop();
            }
            1 => p.dom_proofs.swap(0, 4),
            2 => p.conclusions_wd.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "missing_unary_evidence")
            .expect_err("complete original domains, candidate and formula required");
    }
}

#[test]
fn unary_limit_algebra_rejects_a_changed_domain_or_pointwise_function() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(NEG);
        let builtin = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut builtin.requirements[7] else {
                panic!("equal domains")
            };
            f.left = Obj::StandardSet(StandardSet::RPos);
        } else {
            let Fact::ForallFact(f) = &mut builtin.requirements[9] else {
                panic!("formula")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("formula equality")
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) = &mut f.right else {
                panic!("negation")
            };
            p.arg = Box::new(Obj::StandardSet(StandardSet::R));
        }
        compiler
            .compile_run(&run, "changed_unary_subject")
            .expect_err("exact complete domains and pointwise input function");
    }
}

#[test]
fn unary_limit_algebra_rejects_a_changed_output_limit_or_approach() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(NEG);
        let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
        else {
            panic!("output candidate")
        };
        if mutation == 0 {
            f.value = Obj::StandardSet(StandardSet::R);
        } else {
            f.approach = LimitApproach::AtPositiveInfinity;
        }
        compiler
            .compile_run(&run, "changed_unary_output")
            .expect_err("recorded operation and approach");
    }
}

#[test]
fn unary_limit_parameters_replay_real_scalars_and_natural_exponents() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_scale_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_scale_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_scale_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_scale_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_scale_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_at_power_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_power_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_power_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_power_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_power_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_natural_power_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_guarded_neg_by_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "parameterized_limit").unwrap();
    }
}

#[test]
fn unary_limit_parameters_reject_changed_carriers_and_missing_evidence() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_scale_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_natural_power_by_theorem/statement.lit"
        ),
    ] {
        for missing in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            if missing {
                p.dom_proofs.remove(9);
            } else {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[9]
                else {
                    panic!("operation parameter membership")
                };
                f.set = Obj::StandardSet(StandardSet::C);
            }
            compiler
                .compile_run(&run, "invalid_operation_parameter")
                .expect_err("real/natural parameter evidence is required");
        }
    }
}
