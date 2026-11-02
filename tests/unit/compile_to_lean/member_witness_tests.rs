use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchProofByBuiltinRule, ExistShapedFactSearchedProof,
};
use crate::prelude::*;

const EQUALITY: &str = include_str!("../../../lean/examples/member_equality_witness/statement.lit");
const NONEMPTY: &str = include_str!("../../../lean/examples/nonempty_member_witness/statement.lit");

pub(super) fn witness(run: &mut RunLitexCodeResult) -> &mut VerifyPlainExistFactSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall body");
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &mut body.proof_steps[0]
    else {
        panic!("original proof step");
    };
    let VerifyFactResult::ExistShapedFact(result) = &mut statement.verify_result else {
        panic!("existential result");
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        result.as_mut()
    else {
        panic!("plain-exist success");
    };
    p
}

fn child(p: &mut VerifyPlainExistFactSuccess) -> &mut VerifyFactResult {
    match &mut p.searched_proof {
        ExistShapedFactSearchedProof::ByBuiltinRule(
            ExistShapedFactSearchProofByBuiltinRule::EqualityWitnessFromMembership(p),
        ) => &mut p.membership_proof,
        ExistShapedFactSearchedProof::ByBuiltinRule(
            ExistShapedFactSearchProofByBuiltinRule::NonemptySetMemberWitness(p),
        ) => &mut p.nonempty_proof,
        _ => panic!("actual selected member witness rule"),
    }
}

#[test]
fn member_witnesses_replay_selected_generic_rules_and_both_equalities() {
    for (source, law) in [
        (EQUALITY, "memberEqualityWitness"),
        (NONEMPTY, "nonemptyMemberWitness"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let _ = child(witness(&mut run));
        let output = compiler
            .compile_run(&run, "member_witness")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "member_witness").unwrap()
        );
    }
    for source in [
        EQUALITY.replace("x=a", "a=x"),
        "forall A set,a A:\n    exist x A st {x=a}\n".into(),
        "forall A nonempty_set:\n    exist x A st {x $in A}\n".into(),
        "2 $in {1,2}\nexist x {1,2} st {x=2}\n".into(),
        "2 $in {1,2}\nexist x {1,2} st {2=x}\n".into(),
        "$is_nonempty_set({1})\nexist x {1} st {x $in {1}}\n".into(),
    ] {
        let (run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "orientation_and_constructor")
            .unwrap_or_else(|e| panic!("{e}"));
    }
}

#[test]
fn member_witnesses_require_original_subject_and_prior_citation() {
    for source in [EQUALITY, NONEMPTY] {
        for mutation in ["subject", "future"] {
            let (mut run, compiler) = super::execute(source);
            let p = witness(&mut run);
            let goal_id = p.fact.plain().fact_id;
            let atomic = super::atomic_proof_mut(child(p));
            match mutation {
                "subject" => match &mut atomic.fact {
                    AtomicFact::InFact(f) => f.set = Obj::StandardSet(StandardSet::R),
                    AtomicFact::IsNonemptySetFact(f) => f.set = Obj::StandardSet(StandardSet::R),
                    _ => panic!(),
                },
                "future" => {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut atomic.searched_proof
                    else {
                        panic!("original preceding premise")
                    };
                    cite.cite_fact_id = goal_id;
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("source membership/nonemptiness and preceding citation are mandatory");
        }
    }
}

#[test]
fn member_witnesses_reject_changed_binders_carriers_and_bodies() {
    for source in [EQUALITY, NONEMPTY] {
        for mutation in ["binder", "carrier", "body"] {
            let (mut run, compiler) = super::execute(source);
            let ExistShapedFact::Exist(fact) = &mut witness(&mut run).fact else {
                panic!()
            };
            match mutation {
                "binder" => {
                    fact.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
                }
                "carrier" => {
                    fact.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                "body" => fact.facts.clear(),
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("retain original existential schema and WD");
        }
    }
}
