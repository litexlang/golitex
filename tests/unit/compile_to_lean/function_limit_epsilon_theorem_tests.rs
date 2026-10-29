use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/function_limit_at_from_epsilon_by_theorem/statement.lit");

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
        panic!("explicit epsilon theorem")
    };
    p
}

#[test]
fn function_limit_from_epsilon_replays_five_approaches_and_a_guarded_domain() {
    for source in [
        SOURCE,
        include_str!(
            "../../../lean/examples/function_limit_left_from_epsilon_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_right_from_epsilon_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_from_epsilon_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_from_epsilon_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_guarded_from_epsilon_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "explicit_epsilon")
            .unwrap()
            .contains("FunctionLimitOfForall"));
    }
}

#[test]
fn function_limit_from_epsilon_rejects_missing_or_reordered_clause_proofs() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = invocation(&mut run);
        if missing {
            p.dom_proofs.pop();
        } else {
            p.dom_proofs.swap(5, 6);
        }
        compiler
            .compile_run(&run, "bad_epsilon_proofs")
            .expect_err("both ordered source clauses required");
    }
}

#[test]
fn function_limit_from_epsilon_rejects_wrong_accumulation_and_preimage() {
    for accumulation in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if accumulation {
            let Fact::ForallFact(f) = &mut p.requirements[5] else {
                panic!("radius")
            };
            f.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        } else {
            let Fact::ForallFact(f) = &mut p.requirements[6] else {
                panic!("epsilon")
            };
            let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
                panic!("delta")
            };
            let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut e.facts[0] else {
                panic!("control")
            };
            let Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) = &mut s.right else {
                panic!("preimage")
            };
            p.function = Box::new(Obj::StandardSet(StandardSet::R));
        }
        compiler
            .compile_run(&run, "changed_epsilon_subject")
            .expect_err("the exact domain, direction and function are required");
    }
}
