use crate::compile_to_lean::helper::arithmetic_constructor_pairs;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str, &[(&str, usize)])] = &[
    (
        "sequence_selector_alternatives",
        r#"# Apply supplied alternatives through finite real sequence limit and extremum selectors.
forall a seq(R), L R:
    $has_seq_limit(a,L)
    forall s seq(R):
        $has_seq_limit(s,L)
        =>:
            lim(s) = 0 or s(1) = 0
    =>:
        lim(a) = 0 or a(1) = 0

forall a seq(R), L R:
    $has_seq_limsup(a,L)
    forall s seq(R):
        $has_seq_limsup(s,L)
        =>:
            limsup(s) = 0 or s(1) = 0
    =>:
        limsup(a) = 0 or a(1) = 0

forall a seq(R), L R:
    $has_seq_liminf(a,L)
    forall s seq(R):
        $has_seq_liminf(s,L)
        =>:
            liminf(s) = 0 or s(1) = 0
    =>:
        liminf(a) = 0 or a(1) = 0
"#,
        &[
            ("sequenceLimitValue", 1),
            ("sequenceLimsupValue", 1),
            ("sequenceLiminfValue", 1),
        ],
    ),
    (
        "function_limit_selector_alternatives",
        r#"# Apply supplied alternatives through finite-point, sided and infinite real function limit selectors.
forall f fn(t R) R, p,L R:
    $has_limit_at(f,p,L)
    forall g fn(t R) R:
        $has_limit_at(g,p,L)
        =>:
            fn_lim(g,p) = 0 or g(p) = 0
    =>:
        fn_lim(f,p) = 0 or f(p) = 0

forall f fn(t R) R, p,L R:
    $has_limit_left(f,p,L)
    forall g fn(t R) R:
        $has_limit_left(g,p,L)
        =>:
            lim_left(g,p) = 0 or g(p) = 0
    =>:
        lim_left(f,p) = 0 or f(p) = 0

forall f fn(t R) R, p,L R:
    $has_limit_right(f,p,L)
    forall g fn(t R) R:
        $has_limit_right(g,p,L)
        =>:
            lim_right(g,p) = 0 or g(p) = 0
    =>:
        lim_right(f,p) = 0 or f(p) = 0

forall f fn(t R) R, L R:
    $has_limit_pos_inf(f,L)
    forall g fn(t R) R:
        $has_limit_pos_inf(g,L)
        =>:
            lim_pos_inf(g) = 0 or g(0) = 0
    =>:
        lim_pos_inf(f) = 0 or f(0) = 0

forall f fn(t R) R, L R:
    $has_limit_neg_inf(f,L)
    forall g fn(t R) R:
        $has_limit_neg_inf(g,L)
        =>:
            lim_neg_inf(g) = 0 or g(0) = 0
    =>:
        lim_neg_inf(f) = 0 or f(0) = 0
"#,
        &[
            ("finiteFunctionLimitBothValue", 2),
            ("finiteFunctionLimitLeftValue", 2),
            ("finiteFunctionLimitRightValue", 2),
            ("infiniteFunctionLimitPositiveValue", 1),
            ("infiniteFunctionLimitNegativeValue", 1),
        ],
    ),
    (
        "bound_selector_alternatives",
        r#"# Apply supplied alternatives through real extremal selectors with their original candidate certificates.
forall sc77_A set, L R:
    sc77_A $subset R
    $is_real_least_upper_bound(sc77_A,L)
    forall sc77_S set:
        sc77_S $subset R
        $is_real_least_upper_bound(sc77_S,L)
        =>:
            sup(sc77_S) = 0 or 0 $in sc77_S
    =>:
        sup(sc77_A) = 0 or 0 $in sc77_A

forall sc77_A set, L R:
    sc77_A $subset R
    $is_real_greatest_lower_bound(sc77_A,L)
    forall sc77_S set:
        sc77_S $subset R
        $is_real_greatest_lower_bound(sc77_S,L)
        =>:
            inf(sc77_S) = 0 or 0 $in sc77_S
    =>:
        inf(sc77_A) = 0 or 0 $in sc77_A
"#,
        &[("supremumValue", 1), ("infimumValue", 1)],
    ),
    (
        "calculus_selector_alternatives",
        r#"# Apply supplied alternatives through derivative and integral selectors with their original certificates.
forall f fn(t R) R, p,d R:
    $has_derivative_at(f,p,d)
    forall g fn(t R) R:
        $has_derivative_at(g,p,d)
        =>:
            derivative(g,p) = 0 or g(p) = 0
    =>:
        derivative(f,p) = 0 or f(p) = 0

forall f fn(t R) R, a,b,I R:
    $has_riemann_integral(f,a,b,I)
    forall g fn(t R) R:
        $has_riemann_integral(g,a,b,I)
        =>:
            integral(g,a,b) = 0 or g(a) = 0
    =>:
        integral(f,a,b) = 0 or f(a) = 0
"#,
        &[("derivativeValue", 2), ("riemannIntegralValue", 3)],
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
fn selector(proof: &VerifyOrFactSuccess) -> &Obj {
    let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first)) = &proof.fact.facts[0] else {
        panic!()
    };
    &first.left
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    assert!(
        compiler.compile_run(run, "SelectorCorrupt").is_err(),
        "original selector kind,direction,argument evidence and candidate WD must remain exact"
    );
}
#[test]
fn selector_alternatives_replay_actual_constructor_children_and_original_forall_citations() {
    let mut count = 0;
    for (name, source, expected) in SOURCES {
        let (run, compiler) = super::execute(source);
        assert_eq!(run.statement_results.len(), expected.len(), "{name}");
        for (index, (operation, arity)) in expected.iter().enumerate() {
            let p = result(&run, index);
            let OrFactSearchedProof::ByKnownForallFact(app) = &p.searched_proof else {
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
            assert_eq!(app.arg_match_proofs.len(), 4);
            let DetailedForallConclusionArgMatchProof::ByStructure {
                pattern,
                goal_arg,
                child_matches,
            } = app.arg_match_proofs[0].detailed_ref()
            else {
                panic!("original selector constructor match")
            };
            assert_eq!(child_matches.len(), *arity);
            let (kind, pairs) =
                arithmetic_constructor_pairs(pattern, goal_arg).expect("existing selector meaning");
            assert_eq!(kind, *operation);
            assert_eq!(pairs.len(), *arity);
            count += 1;
        }
        compiler.compile_run(&run, "SelectorOriginal").unwrap();
    }
    assert_eq!(count, 12);
}
#[test]
fn selector_catalog_cannot_match_a_different_kind_or_direction_with_the_same_arity() {
    let mut selectors = Vec::new();
    for (_, source, _) in SOURCES {
        let (run, _) = super::execute(source);
        for index in 0..run.statement_results.len() {
            selectors.push(selector(result(&run, index)).clone());
        }
    }
    assert_eq!(selectors.len(), 12);
    for (index, a) in selectors.iter().enumerate() {
        for (other, b) in selectors.iter().enumerate() {
            assert_eq!(arithmetic_constructor_pairs(a, b).is_some(), index == other);
        }
    }
}
#[test]
fn selector_alternatives_require_original_visible_citations() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let original = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let cite = &mut app.as_detailed_mut().unwrap().cite.fact_id;
                let old = *cite;
                *cite = FactId::new(u64::MAX);
                old
            };
            reject(&run, &compiler);
            let OrFactSearchedProof::ByKnownForallFact(app) =
                &mut result_mut(&mut run, index).searched_proof
            else {
                panic!()
            };
            app.as_detailed_mut().unwrap().cite.fact_id = original;
        }
    }
}
#[test]
fn selector_alternatives_retain_every_original_child_match_in_native_order() {
    let mut ordered = 0;
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let removed = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
                    app.as_detailed_mut().unwrap().arg_match_proofs[0]
                        .as_detailed_mut()
                        .unwrap()
                else {
                    panic!()
                };
                child_matches.pop().unwrap()
            };
            reject(&run, &compiler);
            let swapped = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
                    app.as_detailed_mut().unwrap().arg_match_proofs[0]
                        .as_detailed_mut()
                        .unwrap()
                else {
                    panic!()
                };
                child_matches.push(removed);
                if child_matches.len() > 1 {
                    let last = child_matches.len() - 1;
                    child_matches.swap(0, last);
                    true
                } else {
                    false
                }
            };
            if swapped {
                ordered += 1;
                reject(&run, &compiler);
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
                    app.as_detailed_mut().unwrap().arg_match_proofs[0]
                        .as_detailed_mut()
                        .unwrap()
                else {
                    panic!()
                };
                let last = child_matches.len() - 1;
                child_matches.swap(0, last);
            }
        }
    }
    assert_eq!(ordered, 5);
}
#[test]
fn selector_alternatives_require_original_parameter_and_selection_domain_proofs() {
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
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements
                    .pop()
                    .unwrap()
            };
            reject(&run, &compiler);
            let guard = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let requirements = app
                    .as_detailed_mut()
                    .unwrap()
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap();
                requirements.param_type_requirements.push(removed);
                requirements.proof_of_dom_facts.pop().unwrap()
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
                .proof_of_dom_facts
                .push(guard);
        }
    }
}
#[test]
fn selector_alternatives_keep_original_candidate_citations_inside_the_domain_proof() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let original = {
                let OrFactSearchedProof::ByKnownForallFact(app) =
                    &mut result_mut(&mut run, index).searched_proof
                else {
                    panic!()
                };
                let requirements = app
                    .as_detailed_mut()
                    .unwrap()
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap();
                let candidate =
                    super::atomic_proof_mut(requirements.proof_of_dom_facts.last_mut().unwrap());
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut candidate.searched_proof
                else {
                    panic!("original candidate citation")
                };
                let original = cite.cite_fact_id;
                cite.cite_fact_id = FactId::new(u64::MAX);
                original
            };
            reject(&run, &compiler);
            let OrFactSearchedProof::ByKnownForallFact(app) =
                &mut result_mut(&mut run, index).searched_proof
            else {
                panic!()
            };
            let requirements = app
                .as_detailed_mut()
                .unwrap()
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            let candidate =
                super::atomic_proof_mut(requirements.proof_of_dom_facts.last_mut().unwrap());
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut candidate.searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = original;
        }
    }
}
#[test]
fn selector_alternatives_require_original_target_formation() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
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
#[test]
fn selector_hypotheses_and_candidate_certificates_stay_in_their_original_forall() {
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
