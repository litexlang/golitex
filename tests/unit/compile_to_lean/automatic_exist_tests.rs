use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchedProof, VerifyNotExistFactResult,
};
use crate::prelude::*;

const RECIPROCAL: &str =
    include_str!("../../../lean/examples/automatic_unique_reciprocal/statement.lit");
const PAIR: &str = include_str!("../../../lean/examples/automatic_unique_pair/statement.lit");
const NEGATIVE: &str = include_str!("../../../lean/examples/automatic_excluded_copy/statement.lit");

fn searched(run: &mut RunLitexCodeResult, index: usize) -> &mut ExistShapedFactSearchedProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[index]
    else {
        panic!("fact statement")
    };
    let VerifyFactResult::ExistShapedFact(p) = &mut p.verify_result else {
        panic!("existential family")
    };
    match p.as_mut() {
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) => {
            &mut p.searched_proof
        }
        VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(p)) => {
            &mut p.searched_proof
        }
        VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(p)) => {
            &mut p.searched_proof
        }
        _ => panic!("successful existential verification"),
    }
}

fn application(run: &mut RunLitexCodeResult, index: usize) -> &mut SearchProofByKnownForallFact {
    let ExistShapedFactSearchedProof::ByKnownForallFact(p) = searched(run, index) else {
        panic!("the selected route must be automatic forall application")
    };
    p
}

#[test]
fn automatic_exist_families_replay_exact_routes_and_unique_weakening() {
    for source in [RECIPROCAL, PAIR, NEGATIVE] {
        let (mut run, compiler) = super::execute(source);
        let cite = application(&mut run, 1).cite.fact_id;
        if source == RECIPROCAL {
            assert_eq!(
                application(&mut run, 1)
                    .instantiation_requirements
                    .dom_facts
                    .len(),
                1
            );
        }
        if source == PAIR {
            assert!(matches!(
                searched(&mut run, 2),
                ExistShapedFactSearchedProof::ByKnownExistShapedFact(_)
            ));
            assert_eq!(application(&mut run, 3).cite.fact_id, cite);
        }
        let output = compiler.compile_run(&run, "automatic_exist").unwrap();
        assert!(output.contains(&format!("h_{} (M := M)", cite.value())));
        assert!(output.contains("_exist_match_"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "automatic_exist").unwrap()
        );
    }
}

#[test]
fn automatic_exist_requires_original_arguments_guards_and_citation() {
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = application(&mut run, 1);
        match mutation {
            0 => p.forall_parameters_match_what_args.clear(),
            1 => p.arg_match_proofs.clear(),
            2 => {
                let last = p.arg_match_proofs.len() - 1;
                p.arg_match_proofs.swap(0, last);
            }
            3 => p.instantiation_requirements.param_type_requirements.clear(),
            4 => p.instantiation_requirements.dom_facts.clear(),
            5 => p.instantiation_requirements.proof_of_dom_facts.clear(),
            6 => {
                let ForallConclusionLocation::DirectThenFact(location) = &mut p.cite.location
                else {
                    panic!()
                };
                location.then_fact_index = 99;
            }
            7 => {
                // A body premise cannot replace the cited universal declaration.
                p.cite.fact_id = p.instantiation_requirements.dom_facts[0].fact_id();
            }
            8 => {
                p.instantiation_requirements.dom_facts[0] =
                    p.instantiation_requirements.param_type_requirements[0]
                        .type_fact
                        .clone();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_automatic_exist")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn automatic_exist_rejects_reordered_outer_parameters() {
    let (mut run, compiler) = super::execute(PAIR);
    application(&mut run, 1)
        .forall_parameters_match_what_args
        .swap(0, 1);
    assert!(compiler.compile_run(&run, "wrong_outer_arguments").is_err());
}

#[test]
fn automatic_negative_exist_keeps_hypothetical_witness_facts_local() {
    let (run, compiler) = super::execute(NEGATIVE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[1]
    else {
        panic!()
    };
    let VerifyFactResult::ExistShapedFact(result) = &statement.verify_result else {
        panic!()
    };
    let VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(p)) =
        result.as_ref()
    else {
        panic!()
    };
    let public_id = statement.store_and_infer_result.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(compiler.cited_fact_reference(public_id, &before).is_err());
    assert!(compiler.cited_fact_reference(public_id, &after).is_ok());
    for store in &p
        .well_defined_proof
        .introduced_params
        .defined_params
        .store_and_infer_results
    {
        assert!(compiler
            .cited_fact_reference(store.primary_fact_id(), &after)
            .is_err());
    }
    for fact in &p.fact.plain().facts {
        let fact = crate::instantiate::quantifier_free_fact_to_fact(fact.clone());
        assert!(compiler
            .cited_fact_reference(fact.fact_id(), &after)
            .is_err());
    }
}

#[test]
fn existence_does_not_supply_uniqueness_or_missing_division_guards() {
    for source in [
        "witness exist x R st {x^2 = 4} from 2\nexist! y R st {y^2 = 4}\n".to_string(),
        format!(
            "{}have a R\nexist! y R st {{y = 1 / a}}\n",
            RECIPROCAL.split("exist! y R").next().unwrap()
        ),
    ] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}
