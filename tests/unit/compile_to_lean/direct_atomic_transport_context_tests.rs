use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const CHOICE_ALTERNATIVE: &str = r#"# Equal family and choice functions preserve a supplied choice-or-value alternative.
forall sc75_T,sc75_S nonempty_set, g,k fn(t sc75_T) sc75_S, f,h fn(t sc75_T) family_union(sc75_S), a sc75_T, b family_union(sc75_S):
    g = k
    f = h
    $is_choice_function_for(sc75_T,sc75_S,g,f) or f(a) = b
    =>:
        f(a) = h(a)
        $is_choice_function_for(sc75_T,sc75_S,k,h) or h(a) = b
"#;

const SOURCES: &[(&str, &str, &[(usize, bool)])] = &[
    (
        "equality_preserves_negative_membership",
        r#"# Equal objects and equal sets preserve supplied nonmembership and nonsubset facts.
forall sc74_U,sc74_S set, a,b sc74_U:
    a = b
    not a $in sc74_S
    =>:
        not b $in sc74_S

forall sc74_A,sc74_B,sc74_X,sc74_Y set:
    sc74_A = sc74_X
    sc74_B = sc74_Y
    not sc74_A $subset sc74_B
    =>:
        not sc74_X $subset sc74_Y
"#,
        &[(2, false), (2, false)],
    ),
    (
        "equality_preserves_negative_order",
        r#"# Equal real values preserve all four supplied negative comparisons.
forall a,b,c,d R:
    a = c
    b = d
    not a < b
    =>:
        not c < d

forall a,b,c,d R:
    a = c
    b = d
    not a <= b
    =>:
        not c <= d

forall a,b,c,d R:
    a = c
    b = d
    not a > b
    =>:
        not c > d

forall a,b,c,d R:
    a = c
    b = d
    not a >= b
    =>:
        not c >= d
"#,
        &[(2, false), (2, false), (2, false), (2, false)],
    ),
    (
        "equality_preserves_matrix_inverse_properties",
        r#"# Equal square matrices preserve supplied inverse-candidate and invertibility facts.
forall n N, sc74_A,sc74_B,sc74_X,sc74_Y matrix(C,n,n):
    sc74_A = sc74_X
    sc74_B = sc74_Y
    $is_matrix_inv(sc74_A,sc74_B,n)
    =>:
        $is_matrix_inv(sc74_X,sc74_Y,n)

forall n N, sc74_A,sc74_B matrix(C,n,n):
    sc74_A = sc74_B
    $matrix_inversible(sc74_A,n)
    =>:
        $matrix_inversible(sc74_B,n)

forall n N, sc74_A,sc74_B,sc74_X,sc74_Y matrix(C,n,n):
    sc74_A = sc74_X
    sc74_B = sc74_Y
    not $is_matrix_inv(sc74_A,sc74_B,n)
    =>:
        not $is_matrix_inv(sc74_X,sc74_Y,n)

forall n N, sc74_A,sc74_B matrix(C,n,n):
    sc74_A = sc74_B
    not $matrix_inversible(sc74_A,n)
    =>:
        not $matrix_inversible(sc74_B,n)
"#,
        &[(3, true), (2, true), (3, false), (2, false)],
    ),
    (
        "equality_preserves_indexed_choice",
        r#"# Equal families and choices preserve supplied indexed choice-function facts.
forall sc74_T,sc74_S nonempty_set, g,k fn(t sc74_T) sc74_S, f,h fn(t sc74_T) family_union(sc74_S):
    g = k
    f = h
    $is_choice_function_for(sc74_T,sc74_S,g,f)
    =>:
        $is_choice_function_for(sc74_T,sc74_S,k,h)

forall sc74_T,sc74_S nonempty_set, g,k fn(t sc74_T) sc74_S, f,h fn(t sc74_T) family_union(sc74_S):
    g = k
    f = h
    not $is_choice_function_for(sc74_T,sc74_S,g,f)
    =>:
        not $is_choice_function_for(sc74_T,sc74_S,k,h)
"#,
        &[(4, true), (4, false)],
    ),
];
fn result(run: &RunLitexCodeResult, index: usize) -> &VerifyAtomicExceptEqualityFactSuccess {
    let outer = super::forall_proof(&run.statement_results[index]);
    let VerifyFactResult::AtomicExceptEquality(p) = &outer.proved_then_facts[0].verify_result
    else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn result_mut(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[index]);
    super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn citation(
    p: &VerifyAtomicExceptEqualityFactSuccess,
    wd: bool,
) -> &AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    if wd {
        let PredicateDomainProof::ByKnownFact(c) =
            &p.well_defined_proof.as_detailed().unwrap().predicate_domain
        else {
            panic!("original cached WD citation")
        };
        c
    } else {
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = &p.searched_proof else {
            panic!("original truth citation")
        };
        c
    }
}
fn citation_mut(
    p: &mut VerifyAtomicExceptEqualityFactSuccess,
    wd: bool,
) -> &mut AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    if wd {
        let PredicateDomainProof::ByKnownFact(c) = &mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        else {
            panic!("original cached WD citation")
        };
        c
    } else {
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = &mut p.searched_proof
        else {
            panic!("original truth citation")
        };
        c
    }
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    assert!(
        compiler.compile_run(run, "DirectAtomicCorrupt").is_err(),
        "original truth/WD citations, polarity and all ordered equality paths must remain exact"
    );
}

#[test]
fn direct_atomic_transports_replay_actual_truth_and_cached_wd_citations() {
    let mut count = 0;
    for (name, source, expected) in SOURCES {
        let (run, compiler) = super::execute(source);
        assert_eq!(run.statement_results.len(), expected.len(), "{name}");
        for (index, (arity, positive)) in expected.iter().enumerate() {
            let p = result(&run, index);
            let truth = citation(p, false);
            let wd = citation(p, true);
            assert_eq!(truth.cite_fact_id, wd.cite_fact_id);
            let outer = super::forall_proof(&run.statement_results[index]);
            assert!(outer
                .fact
                .dom_facts
                .iter()
                .any(|f| f.fact_id() == truth.cite_fact_id));
            assert_eq!(
                truth.why_parameters_of_known_fact_are_equal_to_givens.len(),
                *arity
            );
            assert_eq!(
                wd.why_parameters_of_known_fact_are_equal_to_givens.len(),
                *arity
            );
            assert_eq!(
                p.well_defined_proof
                    .as_detailed()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .len(),
                *arity
            );
            assert_eq!(
                crate::ast::fact::atomic_fact_has_positive_polarity(&p.fact),
                *positive
            );
            count += 1;
        }
        compiler.compile_run(&run, "DirectAtomicOriginal").unwrap();
    }
    assert_eq!(count, 12);
}
#[test]
fn direct_atomic_transports_require_both_original_visible_citations() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            for wd in [false, true] {
                let c = citation_mut(result_mut(&mut run, index), wd);
                let original = c.cite_fact_id;
                c.cite_fact_id = FactId::new(u64::MAX);
                reject(&run, &compiler);
                citation_mut(result_mut(&mut run, index), wd).cite_fact_id = original;
            }
        }
    }
}
#[test]
fn direct_atomic_transports_require_complete_ordered_equalities_for_truth_and_wd() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            for wd in [false, true] {
                let removed = citation_mut(result_mut(&mut run, index), wd)
                    .why_parameters_of_known_fact_are_equal_to_givens
                    .pop()
                    .unwrap();
                reject(&run, &compiler);
                {
                    let matches = &mut citation_mut(result_mut(&mut run, index), wd)
                        .why_parameters_of_known_fact_are_equal_to_givens;
                    matches.push(removed);
                    let last = matches.len() - 1;
                    matches.swap(0, last);
                }
                reject(&run, &compiler);
                let matches = &mut citation_mut(result_mut(&mut run, index), wd)
                    .why_parameters_of_known_fact_are_equal_to_givens;
                let last = matches.len() - 1;
                matches.swap(0, last);
            }
        }
    }
}
#[test]
fn direct_choice_transports_cannot_discard_the_truth_irrelevant_family_set_equality() {
    let (_, source, _) = &SOURCES[3];
    let (mut run, compiler) = super::execute(source);
    for index in 0..run.statement_results.len() {
        for wd in [false, true] {
            {
                let matches = &mut citation_mut(result_mut(&mut run, index), wd)
                    .why_parameters_of_known_fact_are_equal_to_givens;
                assert_eq!(matches.len(), 4);
                matches.swap(1, 2);
            }
            reject(&run, &compiler);
            citation_mut(result_mut(&mut run, index), wd)
                .why_parameters_of_known_fact_are_equal_to_givens
                .swap(1, 2);
        }
    }
}
#[test]
fn direct_atomic_transports_preserve_original_polarity() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let p = result_mut(&mut run, index);
            let original = p.fact.clone();
            p.fact = crate::ast::fact::negate_atomic_fact(&p.fact, p.fact.fact_id()).unwrap();
            reject(&run, &compiler);
            result_mut(&mut run, index).fact = original;
        }
    }
}
#[test]
fn direct_atomic_transports_require_original_argument_formation_before_reusing_domains() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let removed = result_mut(&mut run, index)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .pop()
                .unwrap();
            reject(&run, &compiler);
            result_mut(&mut run, index)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .push(removed);
        }
    }
}
#[test]
fn direct_atomic_transports_do_not_publish_private_predicate_or_equality_hypotheses() {
    for (_, source, _) in SOURCES {
        let (run, compiler) = super::execute(source);
        let position =
            SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
        for statement in &run.statement_results {
            let outer = super::forall_proof(statement);
            for fact in &outer.fact.dom_facts {
                assert!(compiler
                    .cited_fact_reference(fact.fact_id(), &position)
                    .is_err());
            }
        }
    }
}
#[test]
fn raw_transport_remains_closed_for_an_unmodeled_predicate_family() {
    let (run, compiler) = super::execute(SOURCES[0].1);
    let original = &result(&run, 0).fact;
    let object = crate::ast::fact::atomic_fact_args_ref(original)[0].clone();
    let unmodeled = AtomicFact::CommRingFact(CommRingFact {
        fact_id: original.fact_id(),
        carrier: object.clone(),
        add: object.clone(),
        mul: object.clone(),
        neg: object.clone(),
        zero: object.clone(),
        one: object,
        line_file: None,
    });
    let position = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(compiler
        .compile_atomic_raw_proposition(&unmodeled, &vec!["_raw_value".into(); 6], &position)
        .is_err());
}

fn choice_alternative_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let VerifyFactResult::OrFact(p) = &mut outer.proved_then_facts[1].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
#[test]
fn the_same_choice_meaning_replays_the_original_or_citation_after_its_explicit_value_equality() {
    let (mut run, compiler) = super::execute(CHOICE_ALTERNATIVE);
    let outer = super::forall_proof(&run.statement_results[0]);
    let source_ids = outer
        .fact
        .dom_facts
        .iter()
        .map(Fact::fact_id)
        .collect::<Vec<_>>();
    let p = choice_alternative_mut(&mut run);
    let OrFactSearchedProof::ByKnownOrFact(app) = &p.searched_proof else {
        panic!("original known-or citation")
    };
    assert!(source_ids.contains(&app.cite_fact_id));
    assert_eq!(
        app.why_parameters_of_known_fact_are_equal_to_givens.len(),
        6
    );
    compiler
        .compile_run(&run, "ChoiceAlternativeOriginal")
        .unwrap();
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(CHOICE_ALTERNATIVE);
        let p = choice_alternative_mut(&mut run);
        let OrFactSearchedProof::ByKnownOrFact(app) = &mut p.searched_proof else {
            panic!()
        };
        match mutation {
            0 => app.cite_fact_id = FactId::new(u64::MAX),
            1 => {
                app.why_parameters_of_known_fact_are_equal_to_givens.pop();
            }
            2 => app
                .why_parameters_of_known_fact_are_equal_to_givens
                .swap(1, 2),
            3 => {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .branches
                    .pop();
            }
            _ => unreachable!(),
        }
        reject(&run, &compiler);
    }
}
