use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchedProof, VerifyNotExistFactResult,
};
use crate::prelude::*;

const RECIPROCAL: &str = r#"# A nonzero real has a unique reciprocal value; instantiate the guarded theorem automatically.
thm unique_reciprocal:
    ? forall seed R:
        seed != 0
        =>:
            exist! x R st {x = 1 / seed}
    witness exist! x R st {x = 1 / seed} from 1 / seed
exist! y R st {y = 1 / 2}
obtain a from exist! z R st {z = 1 / 2}
a = 1 / 2
"#;
const PAIR: &str = r#"# Two real coordinates have a unique specified pair, and unique existence implies existence.
thm unique_pair:
    ? forall first, second R:
        exist! x, y R st {x = first, y = second}
    witness exist! x, y R st {x = first, y = second} from first, second
exist! u, v R st {u = 2, v = 3}
exist s, t R st {s = 2, t = 3}
exist p, q R st {p = 4, q = 5}
obtain a, b from exist x, y R st {x = 4, y = 5}
a = 4
b = 5
"#;
const NEGATIVE: &str = r#"# No real number can be both equal and unequal to a specified real value.
thm excluded_copy:
    ? forall seed R:
        not exist x R st {x = seed, x != seed}
    by contra:
        ? not exist x R st {x = seed, x != seed}
        obtain bad from exist x R st {x = seed, x != seed}
        impossible bad = seed
not exist y R st {y = 7, y != 7}
"#;

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
        let cite = application(&mut run, 1)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id;
        if source == RECIPROCAL {
            assert_eq!(
                application(&mut run, 1)
                    .detailed_ref()
                    .instantiation_requirements
                    .detailed_ref()
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
            assert_eq!(
                application(&mut run, 3)
                    .as_detailed_mut()
                    .unwrap()
                    .cite
                    .fact_id,
                cite
            );
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
            0 => p
                .as_detailed_mut()
                .unwrap()
                .forall_parameters_match_what_args
                .clear(),
            1 => p.as_detailed_mut().unwrap().arg_match_proofs.clear(),
            2 => {
                let last = p.as_detailed_mut().unwrap().arg_match_proofs.len() - 1;
                p.as_detailed_mut().unwrap().arg_match_proofs.swap(0, last);
            }
            3 => p
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements
                .clear(),
            4 => p
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .dom_facts
                .clear(),
            5 => p
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            6 => {
                let ForallConclusionLocation::DirectThenFact(location) =
                    &mut p.as_detailed_mut().unwrap().cite.location
                else {
                    panic!()
                };
                location.then_fact_index = 99;
            }
            7 => {
                // A body premise cannot replace the cited universal declaration.
                p.as_detailed_mut().unwrap().cite.fact_id = p
                    .detailed_ref()
                    .instantiation_requirements
                    .detailed_ref()
                    .dom_facts[0]
                    .fact_id();
            }
            8 => {
                p.as_detailed_mut()
                    .unwrap()
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .dom_facts[0] = p
                    .detailed_ref()
                    .instantiation_requirements
                    .detailed_ref()
                    .param_type_requirements[0]
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
        .as_detailed_mut()
        .unwrap()
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
        .detailed_ref()
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
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}
