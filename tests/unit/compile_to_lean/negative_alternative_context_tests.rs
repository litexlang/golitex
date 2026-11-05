use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const SOURCES: &[(&str, &str)] = &[
    (
        "negative_strict_order_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall a,b,c,d R:
    a = c
    b = d
    not a < b or a = 0
    =>:
        not c < d or c = 0
"#,
    ),
    (
        "equal_sets_negative_subset_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall sc68_A,sc68_B,sc68_X,sc68_Y set:
    sc68_A = sc68_X
    sc68_B = sc68_Y
    not sc68_A $subset sc68_B or sc68_A = {}
    =>:
        not sc68_X $subset sc68_Y or sc68_X = {}
"#,
    ),
    (
        "negative_weak_order_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall a,b,c,d R:
    a = c
    b = d
    not a <= b or a = 0
    =>:
        not c <= d or c = 0
"#,
    ),
    (
        "negative_greater_order_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall a,b,c,d R:
    a = c
    b = d
    not a > b or a = 0
    =>:
        not c > d or c = 0
"#,
    ),
    (
        "negative_weak_greater_order_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall a,b,c,d R:
    a = c
    b = d
    not a >= b or a = 0
    =>:
        not c >= d or c = 0
"#,
    ),
    (
        "negative_subset_disjunction_instantiation",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
forall sc68_A,sc68_B set:
    forall sc68_S,sc68_T set:
        not sc68_S $subset sc68_T or sc68_S = sc68_T
    =>:
        not sc68_A $subset sc68_B or sc68_A = sc68_B
"#,
    ),
    (
        "negative_named_predicate_alternative",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
prop is_zero_for_equality_alternative(x R):
    x = 0

forall a,b R:
    a = b
    not $is_zero_for_equality_alternative(a) or a = 0
    =>:
        not $is_zero_for_equality_alternative(b) or b = 0
"#,
    ),
    (
        "negative_named_predicate_disjunction_instantiation",
        r#"# Reuse a supplied negative-predicate alternative with its original equality evidence.
prop is_zero_for_equality_alternative(x R):
    x = 0

forall a R:
    forall x R:
        not $is_zero_for_equality_alternative(x) or x = 0
    =>:
        not $is_zero_for_equality_alternative(a) or a = 0
"#,
    ),
    (
        "equal_values_negative_predicate_alternative",
        r#"# Equal real values preserve a supplied nonnegative-or-minus-one alternative.
prop is_below_zero_for_equality_alternative(x R):
    x < 0

forall a,b R:
    a = b
    not $is_below_zero_for_equality_alternative(a) or a = -1
    =>:
        not $is_below_zero_for_equality_alternative(b) or b = -1
"#,
    ),
    (
        "negative_predicate_subset_instantiation",
        r#"# Instantiate a supplied predicate alternative on a subset of the real numbers.
prop is_below_zero_for_equality_alternative(x R):
    x < 0

forall sc69_S set, a sc69_S:
    sc69_S $subset R
    forall x sc69_S:
        not $is_below_zero_for_equality_alternative(x) or x = -1
    =>:
        not $is_below_zero_for_equality_alternative(a) or a = -1
"#,
    ),
];
fn result(run: &RunLitexCodeResult) -> &VerifyOrFactSuccess {
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    let VerifyFactResult::OrFact(p) = &outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn result_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
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
        .compile_run(run, "NegativeAlternativeCorrupt")
        .expect_err("the original signed predicate and evidence must remain exact");
}
#[test]
fn negative_alternatives_keep_the_original_citation_and_complete_signed_subject() {
    for (name, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let p = result(&run);
        let AndChainAtomicFact::AtomicFact(first) = &p.fact.facts[0] else {
            panic!()
        };
        assert!(!crate::ast::fact::atomic_fact_has_positive_polarity(first));
        let arity = crate::ast::fact::or_fact_args_ref(&p.fact).len();
        match &p.searched_proof {
            OrFactSearchedProof::ByKnownForallFact(app) => {
                assert!(name.ends_with("instantiation"));
                assert_eq!(app.detailed_ref().arg_match_proofs.len(), arity);
            }
            OrFactSearchedProof::ByKnownOrFact(app) => {
                assert!(!name.ends_with("instantiation"));
                assert_eq!(
                    app.why_parameters_of_known_fact_are_equal_to_givens.len(),
                    arity
                );
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::ClassicalImplication(_),
            ) => {
                assert!(name.starts_with("negative_named_predicate"));
            }
            _ => panic!("{name}:retain original contextual route"),
        }
        compiler
            .compile_run(&run, "NegativeAlternativeOriginal")
            .unwrap();
    }
}
#[test]
fn negative_alternatives_reject_a_positive_goal_in_place_of_the_negative_branch() {
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
fn negative_alternatives_require_the_original_visible_source_fact() {
    for (name, source) in SOURCES {
        // These two true direct implications are positive controls, not
        // contextual-citation examples. Their selected builtin is checked above.
        if name.starts_with("negative_named_predicate") {
            continue;
        }
        let (mut run, compiler) = super::execute(source);
        match &mut result_mut(&mut run).searched_proof {
            OrFactSearchedProof::ByKnownForallFact(app) => {
                app.as_detailed_mut().unwrap().cite.fact_id = FactId::new(u64::MAX)
            }
            OrFactSearchedProof::ByKnownOrFact(app) => app.cite_fact_id = FactId::new(u64::MAX),
            _ => panic!(),
        }
        reject(&run, &compiler);
    }
}
#[test]
fn negative_alternatives_preserve_ordered_argument_matches() {
    for (name, source) in SOURCES {
        if name.starts_with("negative_named_predicate") {
            continue;
        }
        let (mut run, compiler) = super::execute(source);
        match &mut result_mut(&mut run).searched_proof {
            OrFactSearchedProof::ByKnownForallFact(app) => {
                let matches = &mut app.as_detailed_mut().unwrap().arg_match_proofs;
                let last = matches.len() - 1;
                matches.swap(0, last)
            }
            OrFactSearchedProof::ByKnownOrFact(app) => {
                let matches = &mut app.why_parameters_of_known_fact_are_equal_to_givens;
                let last = matches.len() - 1;
                matches.swap(0, last)
            }
            _ => panic!(),
        }
        reject(&run, &compiler);
    }
}
#[test]
fn negative_alternatives_retain_both_original_branch_formations() {
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
fn negative_alternative_hypotheses_stay_local_to_the_original_forall() {
    for (_, source) in SOURCES {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let position =
            SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
        for fact in &outer.fact.dom_facts {
            assert!(compiler
                .cited_fact_reference(fact.fact_id(), &position)
                .is_err());
        }
        compiler
            .compile_run(&run, "NegativeAlternativeClosed")
            .unwrap();
    }
}
