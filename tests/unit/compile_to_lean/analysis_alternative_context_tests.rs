use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str, &[(&str, bool)])] = &[
    (
        "pointwise_regularity_alternatives",
        r#"# Apply supplied pointwise continuity and differentiability alternatives on real subsets.
forall sc72_D set, f fn(t R) R, p sc72_D:
    sc72_D $subset R
    forall x sc72_D:
        $is_continuous_left(f,x) or x = 0
    =>:
        $is_continuous_left(f,p) or p = 0

forall sc72_D set, f fn(t R) R, p sc72_D:
    sc72_D $subset R
    forall x sc72_D:
        not $is_continuous_right(f,x) or x = 0
    =>:
        not $is_continuous_right(f,p) or p = 0

forall sc72_D set, f fn(t R) R, p sc72_D:
    sc72_D $subset R
    forall x sc72_D:
        $is_continuous_at(f,x) or x = 0
    =>:
        $is_continuous_at(f,p) or p = 0

forall sc72_D set, f fn(t R) R, p sc72_D:
    sc72_D $subset R
    forall x sc72_D:
        $is_differentiable_at(f,x) or x = 0
    =>:
        $is_differentiable_at(f,p) or p = 0

forall sc72_D set, f fn(t R) R, p sc72_D:
    sc72_D $subset R
    forall x sc72_D:
        not $is_differentiable_at(f,x) or x = 0
    =>:
        not $is_differentiable_at(f,p) or p = 0
"#,
        &[
            ("is_continuous_left", true),
            ("is_continuous_right", false),
            ("is_continuous_at", true),
            ("is_differentiable_at", true),
            ("is_differentiable_at", false),
        ],
    ),
    (
        "global_regularity_alternatives",
        r#"# Apply supplied global continuity and Lipschitz alternatives to real functions.
forall f fn(t R) R, a R:
    forall g fn(t R) R:
        $is_continuous(g) or g(a) = 0
    =>:
        $is_continuous(f) or f(a) = 0

forall f fn(t R) R, a R:
    forall g fn(t R) R:
        $is_uniformly_continuous(g) or g(a) = 0
    =>:
        $is_uniformly_continuous(f) or f(a) = 0

forall f fn(t R) R, a R:
    forall g fn(t R) R:
        not $is_uniformly_continuous(g) or g(a) = 0
    =>:
        not $is_uniformly_continuous(f) or f(a) = 0

forall f fn(t R) R, K R:
    K >= 0
    forall L R:
        L >= 0
        =>:
            $is_lipschitz(f,L) or L = 0
    =>:
        $is_lipschitz(f,K) or K = 0

forall f fn(t R) R, K R:
    K >= 0
    forall L R:
        L >= 0
        =>:
            not $is_lipschitz(f,L) or L = 0
    =>:
        not $is_lipschitz(f,K) or K = 0
"#,
        &[
            ("is_continuous", true),
            ("is_uniformly_continuous", true),
            ("is_uniformly_continuous", false),
            ("is_lipschitz", true),
            ("is_lipschitz", false),
        ],
    ),
    (
        "accumulation_point_alternatives",
        r#"# Apply supplied one-sided and two-sided accumulation alternatives on real sets.
forall sc72_S set, a R:
    sc72_S $subset R
    forall x R:
        $is_real_accumulation_left(sc72_S,x) or x = 0
    =>:
        $is_real_accumulation_left(sc72_S,a) or a = 0

forall sc72_S set, a R:
    sc72_S $subset R
    forall x R:
        not $is_real_accumulation_right(sc72_S,x) or x = 0
    =>:
        not $is_real_accumulation_right(sc72_S,a) or a = 0

forall sc72_S set, a R:
    sc72_S $subset R
    forall x R:
        $is_real_accumulation_at(sc72_S,x) or x = 0
    =>:
        $is_real_accumulation_at(sc72_S,a) or a = 0
"#,
        &[
            ("is_real_accumulation_left", true),
            ("is_real_accumulation_right", false),
            ("is_real_accumulation_at", true),
        ],
    ),
    (
        "real_set_bound_alternatives",
        r#"# Apply supplied directional bounds and boundedness alternatives to real sets.
forall sc72_S set, a R:
    sc72_S $subset R
    forall x R:
        $is_real_upper_bound(sc72_S,x) or x = 0
    =>:
        $is_real_upper_bound(sc72_S,a) or a = 0

forall sc72_S set, a R:
    sc72_S $subset R
    forall x R:
        not $is_real_lower_bound(sc72_S,x) or x = 0
    =>:
        not $is_real_lower_bound(sc72_S,a) or a = 0

forall sc72_A set:
    sc72_A $subset R
    forall sc72_S set:
        sc72_S $subset R
        =>:
            $is_real_bounded_above(sc72_S) or sc72_S = {}
    =>:
        $is_real_bounded_above(sc72_A) or sc72_A = {}

forall sc72_A set:
    sc72_A $subset R
    forall sc72_S set:
        sc72_S $subset R
        =>:
            not $is_real_bounded_below(sc72_S) or sc72_S = {}
    =>:
        not $is_real_bounded_below(sc72_A) or sc72_A = {}

forall sc72_A set:
    sc72_A $subset R
    forall sc72_S set:
        sc72_S $subset R
        =>:
            not $is_real_bounded(sc72_S) or sc72_S = {}
    =>:
        not $is_real_bounded(sc72_A) or sc72_A = {}
"#,
        &[
            ("is_real_upper_bound", true),
            ("is_real_lower_bound", false),
            ("is_real_bounded_above", true),
            ("is_real_bounded_below", false),
            ("is_real_bounded", false),
        ],
    ),
    (
        "riemann_integral_alternatives",
        r#"# Apply supplied integral-candidate and interval-integrability alternatives.
forall sc72_D set, f fn(t R) R, a,b R, I sc72_D:
    sc72_D $subset R
    forall J sc72_D:
        $has_riemann_integral(f,a,b,J) or J = 0
    =>:
        $has_riemann_integral(f,a,b,I) or I = 0

forall f fn(t R) R, a,b R:
    forall u R:
        $is_riemann_integrable(f,a,u) or u = 0
    =>:
        $is_riemann_integrable(f,a,b) or b = 0

forall sc72_D set, f fn(t R) R, a,b R, I sc72_D:
    sc72_D $subset R
    forall J sc72_D:
        not $has_riemann_integral(f,a,b,J) or J = 0
    =>:
        not $has_riemann_integral(f,a,b,I) or I = 0

forall f fn(t R) R, a,b R:
    forall u R:
        not $is_riemann_integrable(f,a,u) or u = 0
    =>:
        not $is_riemann_integrable(f,a,b) or b = 0
"#,
        &[
            ("has_riemann_integral", true),
            ("is_riemann_integrable", true),
            ("has_riemann_integral", false),
            ("is_riemann_integrable", false),
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
        .compile_run(run, "AnalysisAlternativeCorrupt")
        .expect_err(
            "the original analysis predicate and its complete captured evidence must remain exact",
        );
}

#[test]
fn analysis_alternatives_replay_all_original_selected_citations_and_fixed_predicates() {
    let mut count = 0;
    for (name, source, expected) in SOURCES {
        let (run, compiler) = super::execute(source);
        assert_eq!(run.statement_results.len(), expected.len(), "{name}");
        for (index, (predicate, positive)) in expected.iter().enumerate() {
            let proof = result(&run, index);
            let OrFactSearchedProof::ByKnownForallFact(app) = &proof.searched_proof else {
                panic!("{name}:{index}: original known-forall route");
            };
            let detailed = app.detailed_ref();
            let outer = super::forall_proof(&run.statement_results[index]);
            assert!(outer
                .fact
                .dom_facts
                .iter()
                .any(|f| f.fact_id() == detailed.cite.fact_id));
            assert_eq!(detailed.forall_parameters_match_what_args.len(), 1);
            assert_eq!(
                detailed.arg_match_proofs.len(),
                crate::ast::fact::or_fact_args_ref(&proof.fact).len()
            );
            assert_eq!(proof.well_defined_proof.detailed_ref().branches.len(), 2);
            let AndChainAtomicFact::AtomicFact(first) = &proof.fact.facts[0] else {
                panic!()
            };
            assert_eq!(first.prop_name().local_name(), *predicate);
            assert_eq!(
                crate::ast::fact::atomic_fact_has_positive_polarity(first),
                *positive
            );
            count += 1;
        }
        compiler
            .compile_run(&run, "AnalysisAlternativeOriginal")
            .unwrap();
    }
    assert_eq!(count, 22);
}
#[test]
fn analysis_alternative_hypotheses_remain_private_with_multiple_following_statements() {
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
fn analysis_alternatives_require_original_visible_source_citations() {
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
                let original = *cite;
                *cite = FactId::new(u64::MAX);
                original
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
fn analysis_alternatives_require_every_original_argument_certificate_in_order() {
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
fn analysis_alternatives_retain_original_parameter_membership_and_guard_proofs() {
    let mut guarded = 0;
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
                requirements.proof_of_dom_facts.pop()
            };
            if let Some(guard) = guard {
                guarded += 1;
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
    assert_eq!(guarded, 5);
}
#[test]
fn analysis_alternatives_preserve_original_polarity() {
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
fn change_flag(fact: &mut AtomicFact) -> bool {
    macro_rules! flag {
        ($f:expr,$field:ident,$a:path,$b:path) => {{
            $f.$field = if $f.$field == $a { $b } else { $a };
            true
        }};
    }
    match fact {
        AtomicFact::FunctionContinuousAtFact(f) => {
            flag!(f, side, RealApproachSide::Left, RealApproachSide::Right)
        }
        AtomicFact::NotFunctionContinuousAtFact(f) => {
            flag!(f, side, RealApproachSide::Left, RealApproachSide::Right)
        }
        AtomicFact::RealAccumulationFact(f) => {
            flag!(f, side, RealApproachSide::Left, RealApproachSide::Right)
        }
        AtomicFact::NotRealAccumulationFact(f) => {
            flag!(f, side, RealApproachSide::Left, RealApproachSide::Right)
        }
        AtomicFact::FunctionContinuousFact(f) => flag!(
            f,
            property,
            FunctionContinuityProperty::Continuous,
            FunctionContinuityProperty::UniformContinuous
        ),
        AtomicFact::NotFunctionContinuousFact(f) => flag!(
            f,
            property,
            FunctionContinuityProperty::Continuous,
            FunctionContinuityProperty::UniformContinuous
        ),
        AtomicFact::RealSetBoundFact(f) => flag!(
            f,
            direction,
            RealBoundDirection::Upper,
            RealBoundDirection::Lower
        ),
        AtomicFact::NotRealSetBoundFact(f) => flag!(
            f,
            direction,
            RealBoundDirection::Upper,
            RealBoundDirection::Lower
        ),
        AtomicFact::RealSetBoundedFact(f) => flag!(
            f,
            boundedness,
            RealBoundedness::Above,
            RealBoundedness::Below
        ),
        AtomicFact::NotRealSetBoundedFact(f) => flag!(
            f,
            boundedness,
            RealBoundedness::Above,
            RealBoundedness::Below
        ),
        _ => false,
    }
}
#[test]
fn analysis_alternatives_cannot_change_side_direction_or_global_property() {
    let mut changed = 0;
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        for index in 0..run.statement_results.len() {
            let original = first_mut(&mut run, index).clone();
            if change_flag(first_mut(&mut run, index)) {
                changed += 1;
                reject(&run, &compiler);
            }
            *first_mut(&mut run, index) = original;
        }
    }
    assert_eq!(changed, 14);
}
#[test]
fn analysis_alternatives_require_both_original_branch_well_defined_proofs() {
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
