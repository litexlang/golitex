use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::prelude::*;

const SOURCE: &str = r#"# A marked witness supplies the hidden parameter of an elimination lemma.
# The nullary conclusion is an arbitrary proposition, not a truth assumption.
abstract_prop witness_marked(x)
abstract_prop witness_consequence()
abstract_prop witness_step(x,y)
abstract_prop witness_value_consequence(x)

forall a R:
    $witness_marked(a)
    forall y R:
        $witness_marked(y)
        =>:
            $witness_consequence()
    =>:
        $witness_consequence()

forall a R:
    $witness_marked(a)
    forall y R:
        $witness_marked(y)
        =>:
            not $witness_consequence()
    =>:
        not $witness_consequence()

forall a,b R:
    $witness_step(a,b)
    forall u,v R:
        $witness_step(u,v)
        =>:
            $witness_consequence()
    =>:
        $witness_consequence()

forall a R:
    $witness_marked(a)
    forall y R:
        $witness_marked(y)
        =>:
            $witness_value_consequence(0)
    =>:
        $witness_value_consequence(0)
"#;
// statement index, conclusion arity, hidden parameter count, polarity.
const CASES: &[(usize, usize, usize, bool)] = &[
    (4, 0, 1, true),
    (5, 0, 1, false),
    (6, 0, 2, true),
    (7, 1, 1, true),
];

fn atomic(result: &VerifyFactResult) -> &VerifyAtomicExceptEqualityFactSuccess {
    let VerifyFactResult::AtomicExceptEquality(p) = result else {
        panic!("original atomic result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
        panic!("successful atomic result")
    };
    p
}
fn application(run: &RunLitexCodeResult, index: usize) -> &SearchProofByKnownForallFact {
    let outer = super::forall_proof(&run.statement_results[index]);
    let p = atomic(&outer.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) = &p.searched_proof else {
        panic!("original known-forall application")
    };
    p
}
fn application_mut(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut SearchProofByKnownForallFact {
    let outer = super::forall_proof_mut(&mut run.statement_results[index]);
    let p = super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) = &mut p.searched_proof else {
        panic!("original known-forall application")
    };
    p
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    assert!(
        compiler.compile_run(run, "HiddenWitnessCorrupt").is_err(),
        "nullary conclusions retain exact citations, arguments and requirements"
    );
}

#[test]
fn hidden_witnesses_replay_actual_nullary_positive_negative_and_two_parameter_results() {
    let (run, compiler) = super::execute(SOURCE);
    assert_eq!(run.statement_results.len(), 8);
    for &(index, arity, count, positive) in CASES {
        let outer = super::forall_proof(&run.statement_results[index]);
        let p = atomic(&outer.proved_then_facts[0].verify_result);
        let app = application(&run, index).detailed_ref();
        assert_eq!(app.cite.fact_id, outer.fact.dom_facts[1].fact_id());
        assert_eq!(crate::ast::fact::atomic_fact_args_ref(&p.fact).len(), arity);
        assert_eq!(matches!(p.fact, AtomicFact::NormalAtomicFact(_)), positive);
        assert_eq!(app.arg_match_proofs.len(), arity);
        assert_eq!(app.forall_parameters_match_what_args.len(), count);
        let outer_parameters = outer.fact.typed_parameters.ordered_param_ids();
        for (argument, expected) in app
            .forall_parameters_match_what_args
            .iter()
            .zip(outer_parameters)
        {
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = argument else {
                panic!("original ambient witness")
            };
            assert_eq!(*id, expected);
        }
        let requirements = app.instantiation_requirements.detailed_ref();
        assert_eq!(requirements.param_type_requirements.len(), count);
        assert_eq!(requirements.dom_facts.len(), 1);
        assert_eq!(requirements.proof_of_dom_facts.len(), 1);
        let guard = atomic(&requirements.proof_of_dom_facts[0]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &guard.searched_proof
        else {
            panic!("original witness premise citation")
        };
        assert_eq!(cite.cite_fact_id, outer.fact.dom_facts[0].fact_id());
    }
    compiler.compile_run(&run, "HiddenWitnessOriginal").unwrap();
}

#[test]
fn nullary_applications_require_original_citations_arguments_and_all_certificates() {
    let (mut run, compiler) = super::execute(SOURCE);
    for &(index, _, _, _) in CASES {
        let original = application(&run, index).detailed_ref().cite.fact_id;
        application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = FactId::new(u64::MAX);
        reject(&run, &compiler);
        application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = original;

        let argument = application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .forall_parameters_match_what_args
            .pop()
            .unwrap();
        reject(&run, &compiler);
        application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .forall_parameters_match_what_args
            .push(argument);

        let type_proof = application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .pop()
            .unwrap();
        reject(&run, &compiler);
        application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .push(type_proof);

        let guard = application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .proof_of_dom_facts
            .pop()
            .unwrap();
        reject(&run, &compiler);
        application_mut(&mut run, index)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .proof_of_dom_facts
            .push(guard);

        let original = {
            let app = application_mut(&mut run, index).as_detailed_mut().unwrap();
            let requirement = &mut app
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0];
            let guard = super::atomic_proof_mut(requirement);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut guard.searched_proof
            else {
                panic!()
            };
            let original = cite.cite_fact_id;
            cite.cite_fact_id = FactId::new(u64::MAX);
            original
        };
        reject(&run, &compiler);
        let app = application_mut(&mut run, index).as_detailed_mut().unwrap();
        let requirement = &mut app
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .proof_of_dom_facts[0];
        let guard = super::atomic_proof_mut(requirement);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut guard.searched_proof
        else {
            panic!()
        };
        cite.cite_fact_id = original;
    }
}

#[test]
fn hidden_witness_order_empty_match_shape_and_original_local_scope_remain_exact() {
    let (mut run, compiler) = super::execute(SOURCE);
    application_mut(&mut run, 6)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args
        .swap(0, 1);
    reject(&run, &compiler);
    application_mut(&mut run, 6)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args
        .swap(0, 1);

    // Move the real control evidence out, keeping every other result valid.
    let mut control = run.statement_results.pop().unwrap();
    compiler
        .compile_run(&run, "HiddenWitnessWithoutControl")
        .unwrap();
    let outer = super::forall_proof_mut(&mut control);
    let atomic = super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(control_app) =
        &mut atomic.searched_proof
    else {
        panic!()
    };
    let control_matches = &mut control_app.as_detailed_mut().unwrap().arg_match_proofs;
    let extra = control_matches.pop().unwrap();
    application_mut(&mut run, 4)
        .as_detailed_mut()
        .unwrap()
        .arg_match_proofs
        .push(extra);
    reject(&run, &compiler);
    let extra = application_mut(&mut run, 4)
        .as_detailed_mut()
        .unwrap()
        .arg_match_proofs
        .pop()
        .unwrap();
    control_matches.push(extra);
    run.statement_results.push(control);

    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    for &(index, _, _, _) in CASES {
        let outer = super::forall_proof(&run.statement_results[index]);
        for local in &outer.fact.dom_facts {
            assert!(compiler
                .cited_fact_reference(local.fact_id(), &root)
                .is_err());
        }
    }
}
