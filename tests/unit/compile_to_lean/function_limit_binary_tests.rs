use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const SUM: &str =
    include_str!("../../../lean/examples/function_limit_at_add_by_theorem/statement.lit");
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
        panic!("binary limit invocation")
    };
    p
}

#[test]
fn binary_limit_algebra_replays_all_five_approaches() {
    for source in [
        SUM,
        include_str!("../../../lean/examples/function_limit_at_subtract_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_at_multiply_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_add_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_left_subtract_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_left_multiply_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_right_add_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_right_subtract_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_right_multiply_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_pos_inf_add_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_subtract_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_multiply_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_neg_inf_add_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_subtract_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_multiply_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "binary_limit")
            .unwrap()
            .contains("FunctionLimitMapTwo"));
    }
}

#[test]
fn binary_limit_algebra_requires_three_ordered_function_contexts() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SUM);
        let p = invocation(&mut run);
        match mutation {
            0 => {
                p.dom_proofs.pop();
            }
            1 => p.dom_proofs.swap(0, 8),
            2 => p.dom_stores.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "missing_binary_evidence")
            .expect_err("all domains, candidates and the pointwise equation are required");
    }
}

#[test]
fn binary_limit_algebra_rejects_changed_domain_equalities() {
    for index in [7, 11] {
        let (mut run, compiler) = super::execute(SUM);
        let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[index]
        else {
            panic!("domain equality")
        };
        f.left = Obj::StandardSet(StandardSet::RPos);
        compiler
            .compile_run(&run, "changed_binary_domain")
            .expect_err("equal complete domains must be those of the recorded functions");
    }
}

#[test]
fn binary_limit_algebra_rejects_a_changed_formula_or_result() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(SUM);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::ForallFact(f) = &mut p.requirements[14] else {
                panic!("formula")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("equation")
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) = &mut f.right else {
                panic!("sum")
            };
            p.left = Box::new(Obj::StandardSet(StandardSet::R));
        } else {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = &mut p.conclusions[0]
            else {
                panic!("candidate")
            };
            f.approach = LimitApproach::AtPositiveInfinity;
        }
        compiler
            .compile_run(&run, "changed_binary_subject")
            .expect_err("exact pointwise operands and output approach");
    }
}

#[test]
fn division_limits_replay_both_nonzero_obligations_in_all_approaches() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_divide_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_divide_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_divide_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_divide_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_divide_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_guarded_multiply_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "division_limit").unwrap();
    }
}

#[test]
fn division_limits_reject_missing_or_changed_nonzero_evidence() {
    let source =
        include_str!("../../../lean/examples/function_limit_at_divide_by_theorem/statement.lit");
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(source);
        let p = invocation(&mut run);
        if mutation < 2 {
            p.dom_proofs.remove(14 + mutation);
        } else if mutation == 2 {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[14]
            else {
                panic!("nonzero limit")
            };
            f.left = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[15] else {
                panic!("nonzero calls")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("nonzero call")
            };
            f.left = Obj::StandardSet(StandardSet::R);
        }
        compiler
            .compile_run(&run, "invalid_division_limit")
            .expect_err("nonzero limit and nonzero calls have distinct source evidence");
    }
}

#[test]
fn polynomial_limit_chain_keeps_generated_output_bounded() {
    let source =
        include_str!("../../../lean/examples/function_limit_polynomial_chain/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "polynomial_chain").unwrap();
    assert!(
        lean.len() < 1_000_000,
        "a seventeen-statement chain must share earlier certificates"
    );
    assert!(lean.contains("FunctionLimitMapTwo"));
    assert!(lean.contains("finiteFunctionLimitEqCandidate"));
}
