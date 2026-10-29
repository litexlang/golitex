use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::{ExecDefinitionStmtResult, ExecReleaseAndExpandStmtResult};
use crate::prelude::*;

const ACCUMULATION: &str =
    include_str!("../../../lean/examples/function_limit_at_accumulation_by_theorem/statement.lit");
const CONTROL: &str =
    include_str!("../../../lean/examples/function_limit_at_control_by_theorem/statement.lit");

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut p.proof_steps[0]
    else {
        panic!("released projection")
    };
    p
}

#[test]
fn function_limit_projections_replay_five_approaches() {
    for (source, law) in [
        (ACCUMULATION, "FunctionLimitAccumulation"),
        (CONTROL, "FunctionLimitControl"),
        (include_str!("../../../lean/examples/function_limit_left_accumulation_by_theorem/statement.lit"), "FunctionLimitAccumulation"),
        (include_str!("../../../lean/examples/function_limit_right_accumulation_by_theorem/statement.lit"), "FunctionLimitAccumulation"),
        (include_str!("../../../lean/examples/function_limit_pos_inf_accumulation_by_theorem/statement.lit"), "FunctionLimitAccumulation"),
        (include_str!("../../../lean/examples/function_limit_neg_inf_accumulation_by_theorem/statement.lit"), "FunctionLimitAccumulation"),
        (include_str!("../../../lean/examples/function_limit_left_control_by_theorem/statement.lit"), "FunctionLimitControl"),
        (include_str!("../../../lean/examples/function_limit_right_control_by_theorem/statement.lit"), "FunctionLimitControl"),
        (include_str!("../../../lean/examples/function_limit_pos_inf_control_by_theorem/statement.lit"), "FunctionLimitControl"),
        (include_str!("../../../lean/examples/function_limit_neg_inf_control_by_theorem/statement.lit"), "FunctionLimitControl"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler.compile_run(&run, "project_limit").unwrap().contains(law));
    }
}

#[test]
fn function_limit_projections_require_the_ordered_domain_and_candidate_evidence() {
    for source in [ACCUMULATION, CONTROL] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_proofs.swap(0, 4),
                2 => p.dom_stores.clear(),
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "missing_projection_evidence")
                .expect_err("replay the original proofs and stores in order");
        }
    }
}

#[test]
fn function_limit_control_rejects_a_changed_domain_threshold_or_preimage() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(CONTROL);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::ExistFact(e) = &mut p.conclusions[0] else {
            panic!("threshold")
        };
        if mutation == 0 {
            e.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        } else {
            let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut e.facts[0] else {
                panic!("control")
            };
            if mutation == 1 {
                let Obj::SetFormer(SetFormer::SetBuilder(b)) = &mut s.left else {
                    panic!("neighborhood")
                };
                b.param_set = Box::new(Obj::StandardSet(StandardSet::RPos));
            } else {
                let Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) = &mut s.right else {
                    panic!("preimage")
                };
                p.function = Box::new(Obj::StandardSet(StandardSet::R));
            }
        }
        compiler
            .compile_run(&run, "changed_projection_subject")
            .expect_err("threshold, original domain and preimage function are fixed");
    }
}

#[test]
fn released_accumulation_instantiates_a_generic_source_radius_by_its_denotation() {
    let (run, compiler) = super::execute(ACCUMULATION);
    let lean = compiler.compile_run(&run, "generic_limit_radius").unwrap();
    assert!(
        lean.contains("(Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5))")
    );
}
