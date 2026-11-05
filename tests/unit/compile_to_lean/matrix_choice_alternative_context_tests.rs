use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str, &[(&str, bool)])] = &[
    (
        "square_matrix_inverse_alternatives",
        r#"# Apply supplied inverse-candidate and invertibility alternatives to square matrices.
forall n N, sc73_A,sc73_B,sc73_C matrix(C,n,n):
    forall sc73_M matrix(C,n,n):
        $is_matrix_inv(sc73_A,sc73_M,n) or sc73_M = sc73_B
    =>:
        $is_matrix_inv(sc73_A,sc73_C,n) or sc73_C = sc73_B

forall n N, sc73_A,sc73_B matrix(C,n,n):
    forall sc73_M matrix(C,n,n):
        $matrix_inversible(sc73_M,n) or sc73_M = sc73_A
    =>:
        $matrix_inversible(sc73_B,n) or sc73_B = sc73_A

forall n N, sc73_A,sc73_B,sc73_C matrix(C,n,n):
    forall sc73_M matrix(C,n,n):
        not $is_matrix_inv(sc73_A,sc73_M,n) or sc73_M = sc73_B
    =>:
        not $is_matrix_inv(sc73_A,sc73_C,n) or sc73_C = sc73_B

forall n N, sc73_A,sc73_B matrix(C,n,n):
    forall sc73_M matrix(C,n,n):
        not $matrix_inversible(sc73_M,n) or sc73_M = sc73_A
    =>:
        not $matrix_inversible(sc73_B,n) or sc73_B = sc73_A
"#,
        &[
            ("is_matrix_inv", true),
            ("matrix_inversible", true),
            ("is_matrix_inv", false),
            ("matrix_inversible", false),
        ],
    ),
    (
        "indexed_choice_alternatives",
        r#"# Apply supplied choice-function alternatives on an indexed family of sets.
forall sc73_T,sc73_S nonempty_set, g fn(t sc73_T) sc73_S, f fn(t sc73_T) family_union(sc73_S), a sc73_T, b family_union(sc73_S):
    forall h fn(t sc73_T) family_union(sc73_S):
        $is_choice_function_for(sc73_T,sc73_S,g,h) or h(a) = b
    =>:
        $is_choice_function_for(sc73_T,sc73_S,g,f) or f(a) = b

forall sc73_T,sc73_S nonempty_set, g fn(t sc73_T) sc73_S, f fn(t sc73_T) family_union(sc73_S), a sc73_T, b family_union(sc73_S):
    forall h fn(t sc73_T) family_union(sc73_S):
        not $is_choice_function_for(sc73_T,sc73_S,g,h) or h(a) = b
    =>:
        not $is_choice_function_for(sc73_T,sc73_S,g,f) or f(a) = b
"#,
        &[
            ("is_choice_function_for", true),
            ("is_choice_function_for", false),
        ],
    ),
];
fn result(run: &RunLitexCodeResult, index: usize) -> &VerifyOrFactSuccess {
    let outer = super::forall_proof(&run.statement_results[index]);
    let VerifyFactResult::OrFact(p) = &outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn result_mut(run: &mut RunLitexCodeResult, index: usize) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[index]);
    let VerifyFactResult::OrFact(p) = &mut outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn first_mut(run: &mut RunLitexCodeResult, index: usize) -> &mut AtomicFact {
    let AndChainAtomicFact::AtomicFact(first) = &mut result_mut(run, index).fact.facts[0] else {
        panic!()
    };
    first
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "MatrixChoiceAlternativeCorrupt")
        .expect_err(
        "original dimensions, index/family order, polarity and source evidence must remain exact",
    );
}
#[test]
fn matrix_and_choice_alternatives_replay_actual_forall_citations_and_original_ordered_subjects() {
    let mut count = 0;
    for (name, source, expected) in SOURCES {
        let (run, compiler) = super::execute(source);
        assert_eq!(run.statement_results.len(), expected.len(), "{name}");
        for (index, (predicate, positive)) in expected.iter().enumerate() {
            let proof = result(&run, index);
            let OrFactSearchedProof::ByKnownForallFact(app) = &proof.searched_proof else {
                panic!("{name}:{index}:original known-forall route")
            };
            let app = app.detailed_ref();
            let outer = super::forall_proof(&run.statement_results[index]);
            assert!(outer
                .fact
                .dom_facts
                .iter()
                .any(|f| f.fact_id() == app.cite.fact_id));
            assert_eq!(app.forall_parameters_match_what_args.len(), 1);
            assert_eq!(
                app.arg_match_proofs.len(),
                crate::ast::fact::or_fact_args_ref(&proof.fact).len()
            );
            let AndChainAtomicFact::AtomicFact(first) = &proof.fact.facts[0] else {
                panic!()
            };
            assert_eq!(first.prop_name().local_name(), *predicate);
            assert_eq!(
                crate::ast::fact::atomic_fact_has_positive_polarity(first),
                *positive
            );
            let arity = if *predicate == "is_matrix_inv" {
                3
            } else if *predicate == "matrix_inversible" {
                2
            } else {
                4
            };
            assert_eq!(crate::ast::fact::atomic_fact_args_ref(first).len(), arity);
            count += 1;
        }
        compiler
            .compile_run(&run, "MatrixChoiceAlternativeOriginal")
            .unwrap();
    }
    assert_eq!(count, 6);
}
#[test]
fn matrix_and_choice_alternatives_require_original_source_and_parameter_certificates() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let cite = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let cite = &mut app.as_detailed_mut().unwrap().cite.fact_id;
                let original = *cite;
                *cite = FactId::new(u64::MAX);
                original
            };
            reject(&run, &compiler);
            let removed = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let app = app.as_detailed_mut().unwrap();
                app.cite.fact_id = cite;
                app.instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements
                    .pop()
                    .unwrap()
            };
            reject(&run, &compiler);
            let OrFactSearchedProof::ByKnownForallFact(app) =
                &mut result_mut(&mut run, index).searched_proof
            else {
                panic!()
            };
            app.as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements
                .push(removed);
        }
    }
}
#[test]
fn matrix_and_choice_alternatives_require_original_ordered_argument_equalities() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let removed = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                app.as_detailed_mut()
                    .unwrap()
                    .arg_match_proofs
                    .pop()
                    .unwrap()
            };
            reject(&run, &compiler);
            {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let matches = &mut app.as_detailed_mut().unwrap().arg_match_proofs;
                matches.push(removed);
                let last = matches.len() - 1;
                matches.swap(0, last);
            }
            reject(&run, &compiler);
            let OrFactSearchedProof::ByKnownForallFact(app) =
                &mut result_mut(&mut run, index).searched_proof
            else {
                panic!()
            };
            let matches = &mut app.as_detailed_mut().unwrap().arg_match_proofs;
            let last = matches.len() - 1;
            matches.swap(0, last);
        }
    }
}
#[test]
fn matrix_and_choice_alternatives_cannot_change_original_matrix_order_or_indexed_family() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let first = first_mut(&mut run, index);
            let original = first.clone();
            match first {
                AtomicFact::IsMatrixInvFact(f) => f.order = Obj::StandardSet(StandardSet::R),
                AtomicFact::NotIsMatrixInvFact(f) => f.order = Obj::StandardSet(StandardSet::R),
                AtomicFact::MatrixInversibleFact(f) => f.order = Obj::StandardSet(StandardSet::R),
                AtomicFact::NotMatrixInversibleFact(f) => {
                    f.order = Obj::StandardSet(StandardSet::R)
                }
                AtomicFact::IsChoiceFunctionForFact(f) => f.family = f.choice.clone(),
                AtomicFact::NotIsChoiceFunctionForFact(f) => f.family = f.choice.clone(),
                _ => panic!(),
            }
            reject(&run, &compiler);
            *first_mut(&mut run, index) = original;
        }
    }
}
#[test]
fn matrix_and_choice_alternatives_preserve_original_polarity() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let first = first_mut(&mut run, index);
            let original = first.clone();
            *first = crate::ast::fact::negate_atomic_fact(first, first.fact_id()).unwrap();
            reject(&run, &compiler);
            *first_mut(&mut run, index) = original;
        }
    }
}
#[test]
fn matrix_and_choice_alternatives_keep_original_branch_wd_and_local_hypotheses() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            {
                let outer = super::forall_proof(&run.statement_results[index]);
                let position =
                    SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
                for fact in &outer.fact.dom_facts {
                    assert!(compiler
                        .cited_fact_reference(fact.fact_id(), &position)
                        .is_err());
                }
            }
            let removed = result_mut(&mut run, index)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .branches
                .pop()
                .unwrap();
            reject(&run, &compiler);
            result_mut(&mut run, index)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .branches
                .push(removed);
        }
    }
}
