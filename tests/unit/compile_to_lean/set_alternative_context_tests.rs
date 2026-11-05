use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str)] = &[
    (
        "proper_subset_disjunction_instantiation",
        r#"# Instantiate a supplied proper-subset-or-empty alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        sc70_S $proper_subset sc70_T or sc70_S = {}
    =>:
        sc70_A $proper_subset sc70_B or sc70_A = {}
"#,
    ),
    (
        "proper_superset_disjunction_instantiation",
        r#"# Instantiate a supplied proper-superset-or-empty alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        sc70_S $proper_superset sc70_T or sc70_S = {}
    =>:
        sc70_A $proper_superset sc70_B or sc70_A = {}
"#,
    ),
    (
        "superset_disjunction_instantiation",
        r#"# Instantiate a supplied superset-or-empty alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        sc70_S $superset sc70_T or sc70_S = {}
    =>:
        sc70_A $superset sc70_B or sc70_A = {}
"#,
    ),
    (
        "negative_proper_subset_disjunction_instantiation",
        r#"# Instantiate a supplied negative proper-subset alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        not sc70_S $proper_subset sc70_T or sc70_S = {}
    =>:
        not sc70_A $proper_subset sc70_B or sc70_A = {}
"#,
    ),
    (
        "negative_proper_superset_disjunction_instantiation",
        r#"# Instantiate a supplied negative proper-superset alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        not sc70_S $proper_superset sc70_T or sc70_S = {}
    =>:
        not sc70_A $proper_superset sc70_B or sc70_A = {}
"#,
    ),
    (
        "negative_superset_disjunction_instantiation",
        r#"# Instantiate a supplied negative superset alternative for two sets.
forall sc70_A,sc70_B set:
    forall sc70_S,sc70_T set:
        not sc70_S $superset sc70_T or sc70_S = {}
    =>:
        not sc70_A $superset sc70_B or sc70_A = {}
"#,
    ),
    (
        "infinite_set_disjunction_instantiation",
        r#"# Instantiate a supplied infinite-or-empty alternative for a set.
forall sc70_A set:
    forall sc70_S set:
        not $is_finite_set(sc70_S) or sc70_S = {}
    =>:
        not $is_finite_set(sc70_A) or sc70_A = {}
"#,
    ),
    (
        "empty_set_disjunction_instantiation",
        r#"# Instantiate a supplied emptiness alternative for a set.
forall sc70_A set:
    forall sc70_S set:
        not $is_nonempty_set(sc70_S) or sc70_S = {}
    =>:
        not $is_nonempty_set(sc70_A) or sc70_A = {}
"#,
    ),
    (
        "nonmembership_disjunction_instantiation",
        r#"# Instantiate a supplied nonmembership alternative on a generic carrier.
forall sc70_U,sc70_S,sc70_T set, a sc70_U:
    forall x sc70_U:
        not x $in sc70_S or x $in sc70_T
    =>:
        not a $in sc70_S or a $in sc70_T
"#,
    ),
    (
        "negative_sethood_disjunction_instantiation",
        r#"# Instantiate a supplied negative-sethood alternative on a generic carrier.
forall sc70_U set, a sc70_U:
    forall x sc70_U:
        not $is_set(x) or x = 0
    =>:
        not $is_set(a) or a = 0
"#,
    ),
];

fn result(run: &RunLitexCodeResult) -> &VerifyOrFactSuccess {
    let outer = super::forall_proof(&run.statement_results[0]);
    let VerifyFactResult::OrFact(proof) = &outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(proof) = proof.as_ref() else {
        panic!()
    };
    proof
}
fn result_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::OrFact(proof) = &mut outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(proof) = proof.as_mut() else {
        panic!()
    };
    proof
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "SetAlternativeCorrupt")
        .expect_err("the original set predicate, source citation and evidence must remain exact");
}

#[test]
fn set_alternatives_replay_the_actual_selected_forall_with_original_set_predicates() {
    for (name, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let proof = result(&run);
        let OrFactSearchedProof::ByKnownForallFact(app) = &proof.searched_proof else {
            panic!("{name}: original known-forall route");
        };
        let detailed = app.detailed_ref();
        let outer = super::forall_proof(&run.statement_results[0]);
        assert!(outer
            .fact
            .dom_facts
            .iter()
            .any(|f| f.fact_id() == detailed.cite.fact_id));
        assert_eq!(
            detailed.arg_match_proofs.len(),
            crate::ast::fact::or_fact_args_ref(&proof.fact).len()
        );
        assert_eq!(proof.well_defined_proof.detailed_ref().branches.len(), 2);
        let AndChainAtomicFact::AtomicFact(first) = &proof.fact.facts[0] else {
            panic!()
        };
        match *name {
            "proper_subset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::ProperSubsetFact(_)))
            }
            "proper_superset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::ProperSupersetFact(_)))
            }
            "superset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::SupersetFact(_)))
            }
            "negative_proper_subset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotProperSubsetFact(_)))
            }
            "negative_proper_superset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotProperSupersetFact(_)))
            }
            "negative_superset_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotSupersetFact(_)))
            }
            "infinite_set_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotIsFiniteSetFact(_)))
            }
            "empty_set_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotIsNonemptySetFact(_)))
            }
            "nonmembership_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotInFact(_)))
            }
            "negative_sethood_disjunction_instantiation" => {
                assert!(matches!(first, AtomicFact::NotIsSetFact(_)))
            }
            _ => panic!(),
        }
        compiler
            .compile_run(&run, "SetAlternativeOriginal")
            .unwrap();
    }
}
#[test]
fn set_alternatives_reject_unknown_source_citations() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let OrFactSearchedProof::ByKnownForallFact(app) = &mut result_mut(&mut run).searched_proof
        else {
            panic!()
        };
        app.as_detailed_mut().unwrap().cite.fact_id = FactId::new(u64::MAX);
        reject(&run, &compiler);
    }
}
#[test]
fn set_alternatives_require_each_original_parameter_membership_proof() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let OrFactSearchedProof::ByKnownForallFact(app) = &mut result_mut(&mut run).searched_proof
        else {
            panic!()
        };
        app.as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .pop();
        reject(&run, &compiler);
    }
}
#[test]
fn set_alternatives_require_the_original_ordered_argument_certificates() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let OrFactSearchedProof::ByKnownForallFact(app) = &mut result_mut(&mut run).searched_proof
        else {
            panic!()
        };
        let matches = &mut app.as_detailed_mut().unwrap().arg_match_proofs;
        let last = matches.len() - 1;
        matches.swap(0, last);
        reject(&run, &compiler);
    }
}
#[test]
fn set_alternatives_preserve_the_original_predicate_polarity() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let AndChainAtomicFact::AtomicFact(first) = &mut result_mut(&mut run).fact.facts[0] else {
            panic!()
        };
        *first = crate::ast::fact::negate_atomic_fact(first, first.fact_id()).unwrap();
        reject(&run, &compiler);
    }
}
#[test]
fn set_alternatives_require_complete_branch_formation_and_keep_hypotheses_local() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let position = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        for fact in &outer.fact.dom_facts {
            assert!(compiler
                .cited_fact_reference(fact.fact_id(), &position)
                .is_err());
        }
        result_mut(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .branches
            .pop();
        reject(&run, &compiler);
    }
}
