use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::execute::execute_witness_stmt::{
    ExecWitnessExistFactStmtResult, ExecWitnessExistFactStmtSuccessResult, ExecWitnessStmtResult,
};
use crate::execute::{ExecObtainObjFromExistFactStmtResult, ObtainExistVerifySuccess};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferExistUniqueFactResult, InferResult};

const SIMPLE: &str = include_str!("../../../lean/examples/unique_real_zero/statement.lit");
const PAIR: &str = include_str!("../../../lean/examples/unique_real_pair/statement.lit");

fn witness(run: &mut RunLitexCodeResult) -> &mut ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("unique witness")
    };
    p
}
fn uniqueness(proof: &mut ExecWitnessExistFactStmtSuccessResult) -> &mut ForallFact {
    let Some(VerifyFactResult::ForallFact(p)) = &mut proof.obligations.uniqueness_check else {
        panic!("uniqueness check")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_mut()
    else {
        panic!("local forall")
    };
    &mut p.fact
}

#[test]
fn unique_existence_replays_witness_citation_and_obtain() {
    for source in [
        SIMPLE,
        PAIR,
        include_str!("../../../lean/examples/unique_reciprocal_value/statement.lit"),
        include_str!("../../../lean/examples/unique_real_theorem/statement.lit"),
        include_str!("../../../lean/examples/unique_copy_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "unique_example").unwrap();
        assert!(output.contains("_unique_left_"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "unique_example").unwrap()
        );
        if source == PAIR {
            assert!(output.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
        }
        if source == SIMPLE {
            assert!(!output.contains("variable [_functionSemantics"));
        }
    }
}

#[test]
fn unique_witness_requires_the_exact_two_candidate_proof() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(PAIR);
        let p = witness(&mut run);
        match mutation {
            0 => p.obligations.uniqueness_check = None,
            1 => uniqueness(p).dom_facts.pop().map(|_| ()).unwrap(),
            2 => uniqueness(p).dom_facts.swap(0, 1),
            3 => {
                uniqueness(p).typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            4 => {
                let target = uniqueness(p);
                let id = target.typed_parameters.groups[0].params[0].id;
                target.typed_parameters.groups[1].params[0].id = id;
            }
            5 => {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut uniqueness(p).then_facts[0]
                else {
                    panic!()
                };
                let Obj::ProductShape(ProductShape::Tuple(tuple)) = &mut eq.right else {
                    panic!()
                };
                tuple.args.swap(0, 1);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_uniqueness").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn unique_inference_and_obtain_validate_their_recorded_conclusions() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(PAIR);
        if mutation < 3 {
            let p = witness(&mut run);
            if mutation == 0 {
                p.store_and_infer_result.infer = None;
            } else {
                let Some(InferResult::ExistUniqueFact(
                    InferExistUniqueFactResult::UniquenessForall(infer),
                )) = &mut p.store_and_infer_result.infer
                else {
                    panic!()
                };
                let StoreFactResult::ForallFact(stored) = &mut infer.derived.store else {
                    panic!()
                };
                if mutation == 1 {
                    stored.fact.dom_facts.swap(0, 1);
                } else {
                    let ExistOrAndChainAtomicFact::AndFact(and) = &mut stored.fact.then_facts[0]
                    else {
                        panic!()
                    };
                    and.facts.swap(0, 1);
                }
            }
        } else {
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    ExecObtainObjFromExistFactStmtResult::Success(p),
                ),
            )) = &mut run.statement_results[2]
            else {
                panic!()
            };
            if mutation == 3 {
                p.store_and_infer_result.store_and_infer_results.pop();
            } else {
                let ObtainExistVerifySuccess::ExistUnique(verified) = &mut p.verify_exist else {
                    panic!()
                };
                let plain = verified.fact.plain().clone();
                verified.fact = ExistShapedFact::Exist(plain);
            }
        }
        assert!(
            compiler.compile_run(&run, "bad_stored_uniqueness").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn unique_citations_are_published_after_the_witness_and_do_not_export_locals() {
    let (mut run, compiler) = super::execute(SIMPLE);
    let p = witness(&mut run);
    let private_id =
        p.introduced_params.defined_params.store_and_infer_results[0].primary_fact_id();
    let public_id = p.store_and_infer_result.primary_fact_id();
    let Some(InferResult::ExistUniqueFact(InferExistUniqueFactResult::UniquenessForall(infer))) =
        &p.store_and_infer_result.infer
    else {
        panic!()
    };
    let inferred = infer.derived.store.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    for id in [public_id, inferred] {
        assert!(compiler.cited_fact_reference(id, &before).is_err());
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
    }
    assert!(compiler.cited_fact_reference(private_id, &after).is_err());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[1] else {
        panic!()
    };
    let VerifyFactResult::ExistShapedFact(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(known) = &mut p.searched_proof else {
        panic!()
    };
    known.cite_fact_id = inferred;
    assert!(compiler.compile_run(&run, "wrong_unique_citation").is_err());
}

#[test]
fn one_witness_does_not_establish_unique_existence() {
    for source in [
        "witness exist! x R st {x^2 = 4} from 2\n",
        "witness exist! x R st {x = 0} from 1\n",
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
fn unique_existence_known_forall_search_replays_recorded_application() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/automatic_unique_copy/statement.lit"
    ));
    let output = compiler.compile_run(&run, "unique_forall").unwrap();
    assert!(output.contains("_known_unique"));
}
