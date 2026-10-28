use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchedProof, VerifyNotExistFactResult,
};
use crate::execute::ExecObtainObjFromExistFactStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferNotExistFactResult, InferResult};

const SIMPLE: &str = include_str!("../../../lean/examples/no_one_in_zero_singleton/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/nonzero_reciprocal_reflexivity/statement.lit");

fn contra(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("contra")
    };
    p
}

#[test]
fn negative_existence_replays_contra_witness_and_reuse() {
    for source in [
        SIMPLE,
        GUARDED,
        include_str!("../../../lean/examples/incompatible_existential_equalities/statement.lit"),
        include_str!("../../../lean/examples/no_self_unequal_alternative/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "negative_exist").unwrap();
        assert!(output.contains("¬ (∃"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "negative_exist").unwrap()
        );
    }
}

#[test]
fn negative_existence_rejects_changed_negation_formation_and_inference() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(GUARDED);
        let p = contra(&mut run, 0);
        match mutation {
            0 => {
                let Fact::ExistFact(f) = &mut p.reverse_assumption else {
                    panic!()
                };
                f.facts.clear();
            }
            1 => {
                let FactWellDefinedProof::ExistFact(wd) = &mut p.reverse_assumption_wd else {
                    panic!()
                };
                wd.as_detailed_mut().unwrap().assumed_body_facts.clear();
            }
            2 => p.stored.infer = None,
            3 => p.stored.infer = Some(InferResult::NotExistFact(InferNotExistFactResult::NoInfer)),
            4..=6 => {
                let Some(InferResult::NotExistFact(InferNotExistFactResult::DemorganForall(infer))) =
                    &mut p.stored.infer
                else {
                    panic!()
                };
                let StoreFactResult::ForallFact(stored) = &mut infer.derived.store else {
                    panic!()
                };
                match mutation {
                    4 => stored.fact.then_facts.clear(),
                    5 => {
                        stored.fact.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::C))
                    }
                    6 => {
                        let Fact::NotExistFact(source) = &p.goal else {
                            panic!()
                        };
                        let QuantifierFreeFact::AtomicFact(atom) = &source.facts[0] else {
                            panic!()
                        };
                        stored.fact.then_facts[0] =
                            ExistOrAndChainAtomicFact::AtomicFact(atom.clone());
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_negative_exist")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn negative_existence_citations_respect_family_and_scope() {
    let (mut run, compiler) = super::execute(GUARDED);
    let p = contra(&mut run, 0);
    let private_id = p.reverse_assumption_fact_id;
    let Some(InferResult::NotExistFact(InferNotExistFactResult::DemorganForall(infer))) =
        &p.stored.infer
    else {
        panic!()
    };
    let public_id = infer.derived.store.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler.cited_fact_reference(public_id, &before).is_err());
    assert!(compiler.cited_fact_reference(public_id, &after).is_ok());
    assert!(compiler.cited_fact_reference(private_id, &after).is_err());

    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[1] else {
        panic!()
    };
    let VerifyFactResult::ExistShapedFact(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(known) = &mut p.searched_proof else {
        panic!()
    };
    known.cite_fact_id = public_id; // A forall is not the cited negative existential.
    assert!(compiler.compile_run(&run, "wrong_citation").is_err());
}

#[test]
fn existing_witness_and_undefined_reciprocal_are_rejected() {
    for source in [
        "not exist x R st {x = x}\n",
        "not exist x R st {1 / x != 1 / x}\n",
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}

#[test]
fn obtain_returns_become_visible_in_order_inside_contradiction() {
    let (mut run, compiler) = super::execute(GUARDED);
    let p = contra(&mut run, 0);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromExistFact(
            ExecObtainObjFromExistFactStmtResult::Success(obtain),
        ),
    )) = &p.proof_steps[0]
    else {
        panic!("obtain")
    };
    let member = obtain.store_and_infer_result.store_and_infer_results[0].primary_fact_id();
    let guard = obtain.store_and_infer_result.store_and_infer_results[1].primary_fact_id();
    let scope = SourcePosition::new(None, SourceOwner::Contra(p), 2);
    let before_returns =
        SourcePosition::new(Some(&scope), SourceOwner::Statement(&p.proof_steps[0]), 1);
    let member_returned = SourcePosition {
        before: 2,
        ..before_returns
    };
    let guard_returned = SourcePosition {
        before: 3,
        ..before_returns
    };
    assert!(compiler
        .cited_fact_reference(member, &before_returns)
        .is_err());
    assert!(compiler
        .cited_fact_reference(member, &member_returned)
        .is_ok());
    assert!(compiler
        .cited_fact_reference(guard, &member_returned)
        .is_err());
    assert!(compiler
        .cited_fact_reference(guard, &guard_returned)
        .is_ok());
}
