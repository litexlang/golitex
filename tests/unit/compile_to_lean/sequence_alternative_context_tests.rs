use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str)] = &[
    (
        "sequence_limit_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        $has_seq_limit(s,v) or v < s(1)
    =>:
        $has_seq_limit(a,L) or L < a(1)
"#,
    ),
    (
        "equal_sequences_limit_alternative",
        r#"# Equal source sequences preserve the supplied convergence alternative.
forall a,b seq(R), L,K R:
    a = b
    L = K
    $has_seq_limit(a,L) or L = 0
    =>:
        $has_seq_limit(b,K) or K = 0
"#,
    ),
    (
        "equal_sequences_negative_limit_alternative",
        r#"# Equal source sequences preserve the supplied convergence alternative.
forall a,b seq(R), L,K R:
    a = b
    L = K
    not $has_seq_limit(a,L) or L = 0
    =>:
        not $has_seq_limit(b,K) or K = 0
"#,
    ),
    (
        "sequence_limsup_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        $has_seq_limsup(s,v) or v < s(1)
    =>:
        $has_seq_limsup(a,L) or L < a(1)
"#,
    ),
    (
        "sequence_negative_limsup_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        not $has_seq_limsup(s,v) or v < s(1)
    =>:
        not $has_seq_limsup(a,L) or L < a(1)
"#,
    ),
    (
        "sequence_liminf_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        $has_seq_liminf(s,v) or v < s(1)
    =>:
        $has_seq_liminf(a,L) or L < a(1)
"#,
    ),
    (
        "sequence_negative_liminf_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        not $has_seq_liminf(s,v) or v < s(1)
    =>:
        not $has_seq_liminf(a,L) or L < a(1)
"#,
    ),
    (
        "sequence_cauchy_disjunction_instantiation",
        r#"# Instantiate a supplied universal sequence-analysis alternative.
forall a seq(R), L R:
    forall s seq(R), v R:
        $is_seq_cauchy(s) or v < s(1)
    =>:
        $is_seq_cauchy(a) or L < a(1)
"#,
    ),
    (
        "equal_sequences_cauchy_alternative",
        r#"# Equal source sequences preserve the supplied convergence alternative.
forall a,b seq(R), L R:
    a = b
    $is_seq_cauchy(a) or L = 0
    =>:
        $is_seq_cauchy(b) or L = 0
"#,
    ),
    (
        "equal_sequences_negative_cauchy_alternative",
        r#"# Equal source sequences preserve the supplied convergence alternative.
forall a,b seq(R), L R:
    a = b
    not $is_seq_cauchy(a) or L = 0
    =>:
        not $is_seq_cauchy(b) or L = 0
"#,
    ),
];
fn result(run: &RunLitexCodeResult) -> &VerifyOrFactSuccess {
    let outer = super::forall_proof(&run.statement_results[0]);
    let VerifyFactResult::OrFact(p) = &outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn result_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::OrFact(p) = &mut outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "SequenceAlternativeCorrupt")
        .expect_err("altered source predicate or evidence must reject");
}

#[test]
fn sequence_alternatives_replay_the_actual_known_forall_and_known_or_routes() {
    for (name, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let p = result(&run);
        let outer = super::forall_proof(&run.statement_results[0]);
        let arity = crate::ast::fact::or_fact_args_ref(&p.fact).len();
        assert_eq!(p.fact.facts.len(), 2);
        assert_eq!(
            p.well_defined_proof.as_detailed().unwrap().branches.len(),
            2
        );
        let cite = match &p.searched_proof {
            OrFactSearchedProof::ByKnownForallFact(app) => {
                assert!(name.ends_with("instantiation"));
                let app = app.as_detailed().unwrap();
                assert_eq!(app.arg_match_proofs.len(), arity);
                assert_eq!(app.forall_parameters_match_what_args.len(), 2);
                assert_eq!(
                    app.instantiation_requirements
                        .detailed_ref()
                        .param_type_requirements
                        .len(),
                    2
                );
                app.cite.fact_id
            }
            OrFactSearchedProof::ByKnownOrFact(app) => {
                assert!(name.starts_with("equal_"));
                assert_eq!(
                    app.why_parameters_of_known_fact_are_equal_to_givens.len(),
                    arity
                );
                app.cite_fact_id
            }
            _ => panic!("{name}: preserve original contextual evidence"),
        };
        assert!(outer.fact.dom_facts.iter().any(|f| f.fact_id() == cite));
        compiler
            .compile_run(&run, "SequenceAlternativeOriginal")
            .unwrap();
        eprintln!(
            "ORIGINAL {name}: cite={} ordered_arguments={arity}",
            cite.value()
        );
    }
}

#[test]
fn sequence_alternatives_preserve_original_polarity_and_sequence_property() {
    for (name, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let p = result(&run);
        let AndChainAtomicFact::AtomicFact(first) = &p.fact.facts[0] else {
            panic!()
        };
        assert_eq!(
            crate::ast::fact::atomic_fact_has_positive_polarity(first),
            !name.contains("negative")
        );
        if name.contains("cauchy") {
            match first {
                AtomicFact::SequenceAnalysisFact(f) => {
                    assert_eq!(f.property, SequenceAnalysisProperty::Cauchy)
                }
                AtomicFact::NotSequenceAnalysisFact(f) => {
                    assert_eq!(f.property, SequenceAnalysisProperty::Cauchy)
                }
                _ => panic!(),
            }
        }
        compiler
            .compile_run(&run, "SequenceAlternativeOriginalKinds")
            .unwrap();
    }
}

#[test]
fn sequence_alternatives_require_the_original_visible_citation() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        match &mut result_mut(&mut run).searched_proof {
            OrFactSearchedProof::ByKnownForallFact(p) => {
                p.as_detailed_mut().unwrap().cite.fact_id = FactId::new(u64::MAX)
            }
            OrFactSearchedProof::ByKnownOrFact(p) => p.cite_fact_id = FactId::new(u64::MAX),
            _ => panic!(),
        }
        reject(&run, &compiler);
    }
}

#[test]
fn sequence_alternatives_require_every_ordered_argument_certificate() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        match &mut result_mut(&mut run).searched_proof {
            OrFactSearchedProof::ByKnownForallFact(p) => {
                p.as_detailed_mut().unwrap().arg_match_proofs.pop();
            }
            OrFactSearchedProof::ByKnownOrFact(p) => {
                p.why_parameters_of_known_fact_are_equal_to_givens.pop();
            }
            _ => panic!(),
        }
        reject(&run, &compiler);
    }
}

#[test]
fn sequence_alternatives_require_both_original_branch_formations() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        result_mut(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .branches
            .pop();
        reject(&run, &compiler);
    }
}

#[test]
fn sequence_alternatives_reject_a_changed_predicate_polarity() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let p = result_mut(&mut run);
        let AndChainAtomicFact::AtomicFact(first) = &mut p.fact.facts[0] else {
            panic!()
        };
        *first = crate::ast::fact::negate_atomic_fact(first, first.fact_id()).unwrap();
        reject(&run, &compiler);
    }
}

#[test]
fn sequence_alternatives_reject_a_different_sequence_analysis_property() {
    for (name, source) in SOURCES {
        if !name.contains("cauchy") {
            continue;
        }
        let (mut run, compiler) = super::execute(source);
        let AndChainAtomicFact::AtomicFact(first) = &mut result_mut(&mut run).fact.facts[0] else {
            panic!()
        };
        match first {
            AtomicFact::SequenceAnalysisFact(f) => {
                f.property = SequenceAnalysisProperty::Convergent
            }
            AtomicFact::NotSequenceAnalysisFact(f) => {
                f.property = SequenceAnalysisProperty::Convergent
            }
            _ => panic!(),
        }
        reject(&run, &compiler);
    }
}

#[test]
fn sequence_alternatives_do_not_publish_their_local_source_hypotheses() {
    for (_, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let position = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        for fact in &outer.fact.dom_facts {
            assert!(compiler
                .cited_fact_reference(fact.fact_id(), &position)
                .is_err());
        }
        compiler
            .compile_run(&run, "SequenceAlternativeClosed")
            .unwrap();
    }
}
