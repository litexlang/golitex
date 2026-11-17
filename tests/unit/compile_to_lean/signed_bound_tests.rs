use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    less::LessFactSearchProofByBuiltinRule as Less,
    less_equal::LessEqualFactSearchProofByBuiltinRule as Le,
    not_equal::NotEqualFactSearchProofByBuiltinRule as Ne,
};

fn citation(proof: &mut VerifyAtomicExceptEqualityFactSuccess) -> &mut FactId {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof
    else {
        panic!("selected builtin")
    };
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            Ne::NonzeroFromSignedBound(p),
        ) => &mut p.cite_fact_id,
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            Less::OrderSignFromPositiveLiteralBound(p),
        ) => &mut p.cite_fact_id,
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            Le::OrderSignFromNegativeLiteralBound(p),
        ) => &mut p.cite_fact_id,
        _ => panic!("selected signed-bound variant"),
    }
}

const SOURCES: [&str; 3] = [
    r#"forall x R:
    2<=x
    =>:
        x!=0
"#,
    r#"forall x R:
    2<=x
    =>:
        0<x
"#,
    r#"forall x R:
    x<=-2
    =>:
        x<=0
"#,
];

#[test]
fn signed_bounds_replay_the_original_scoped_citation_for_all_three_variants() {
    for source in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let expected = forall.assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        assert_eq!(
            *citation(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result
            )),
            expected
        );
        let output = compiler.compile_run(&run, "signed_bound").unwrap();
        assert!(output.contains(&format!("h_{}", expected.value())));
        assert!(output.contains("Litex.NativeBridge.ltOfDenoteReal"));
        assert_eq!(output, compiler.compile_run(&run, "signed_bound").unwrap());
    }
}

#[test]
fn signed_bounds_preserve_all_orientations_and_strict_thresholds() {
    for (premise, positive) in [
        ("2<=x", true),
        ("x>=2", true),
        ("2<x", true),
        ("x>2", true),
        ("x<=-2", false),
        ("-2>=x", false),
        ("x<-2", false),
        ("-2>x", false),
    ] {
        for goal in ["x!=0", "0!=x", if positive { "0<x" } else { "x<=0" }] {
            let source = format!("forall x R:\n    {premise}\n    =>:\n        {goal}\n");
            let (run, compiler) = super::execute(&source);
            // Existing inference may publish a stronger strict bound and select
            // an earlier rule. Only SOURCES above certify these three variants.
            compiler
                .compile_run(&run, "signed_bound_orientation")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
        }
    }
}

#[test]
fn resolved_positive_bounds_construct_zero_without_a_source_occurrence() {
    let fixture = include_str!("../../fixtures/compile_to_lean/resolved_positive_bound.lit");
    for source in [
        fixture,
        "forall x R:\n    1<=x\n    =>:\n        x $in R+\n",
        "forall x R:\n    x>2\n    =>:\n        x $in R+\n",
        "forall x Q:\n    x>=1/2\n    =>:\n        x $in Q+\n",
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "resolved_positive_bound")
            .unwrap();
        assert!(output.contains("Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)"));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "resolved_positive_bound")
                .unwrap()
        );
    }
}

#[test]
fn resolved_positive_bounds_reject_changed_subject_sign_and_citation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_real_sign_proof::{
        RealSign, StructuralRealSignReason,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;

    let source = include_str!("../../fixtures/compile_to_lean/resolved_positive_bound.lit");
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(source);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let target = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let future = target.fact.fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::SignedNumericMembership(proof),
            ),
        ) = &mut target.searched_proof
        else {
            panic!("resolved positive membership");
        };
        if mutation == 0 {
            proof.sign.sign = RealSign::Nonnegative;
        } else {
            let StructuralRealSignReason::ResolvedBound { real, source } = &mut proof.sign.reason
            else {
                panic!("resolved bound");
            };
            if mutation == 1 {
                real.element = Obj::Literal(Literal::Number(Number::new("7".into())));
            } else {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    source.searched_proof.as_mut()
                else {
                    panic!("known bound citation");
                };
                citation.cite_fact_id = if mutation == 2 {
                    future
                } else {
                    FactId::new(u64::MAX)
                };
            }
        }
        compiler
            .compile_run(&run, "invalid_resolved_positive_bound")
            .expect_err(
                "resolved bounds require their original subject, sign and visible citation",
            );
    }
}

#[test]
fn signed_bound_citations_cannot_escape_scope_or_change_sign_subject_or_strength() {
    for source in SOURCES {
        for change in ["future", "missing", "subject", "sign", "threshold"] {
            let (mut run, compiler) = super::execute(source);
            let forall = super::forall_proof_mut(&mut run.statement_results[0]);
            let target = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let future = target.fact.fact_id();
            if change == "future" || change == "missing" {
                *citation(target) = if change == "future" {
                    future
                } else {
                    FactId::new(u64::MAX)
                };
            } else {
                let StoreFactResult::AtomicFact(stored) =
                    &mut forall.assumed_dom_facts[0].store_and_infer.store
                else {
                    panic!()
                };
                let (bound, value) = match &mut stored.fact {
                    AtomicFact::LessEqualFact(f) if source.contains("2<=x") => {
                        (&mut f.left, &mut f.right)
                    }
                    AtomicFact::LessEqualFact(f) => (&mut f.right, &mut f.left),
                    _ => panic!(),
                };
                if change == "subject" {
                    *value = Obj::Literal(Literal::Number(Number::new("7".into())));
                } else {
                    *bound = Obj::Literal(Literal::Number(Number::new(
                        if change == "threshold" {
                            "0"
                        } else if source.contains("2<=x") {
                            "-2"
                        } else {
                            "2"
                        }
                        .into(),
                    )));
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "original visible bound, signed endpoint and strict threshold are mandatory",
            );
        }
    }
}

#[test]
fn weak_zero_bounds_do_not_prove_a_sign_or_nonzero() {
    for (premise, goal) in [
        ("0<=x", "x!=0"),
        ("0<=x", "0<x"),
        ("0<=x", "x $in R+"),
        ("x>=-1", "x $in R+"),
        ("x<=0", "x!=0"),
        ("x<=2", "x<=0"),
    ] {
        let source = format!("forall x R:\n    {premise}\n    =>:\n        {goal}\n");
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(&source)
                .unwrap()
                .success
        );
    }
}

#[test]
fn signed_bound_citations_use_stable_predicate_priority() {
    for (premises, positive) in [("x>=1\n    x>2", true), ("x<=-1\n    x< -2", false)] {
        // A theorem records both assumptions in an isolated proof scope.
        let source = format!("forall x R:\n    {premises}\n    =>:\n        x=x\n");
        for _ in 0..16 {
            let (mut run, mut compiler) = super::execute(&source);
            let forall = super::forall_proof_mut(&mut run.statement_results[0]);
            let expected = forall.assumed_dom_facts[0]
                .store_and_infer
                .primary_fact_id();
            let Fact::AtomicFact(bound) = &forall.fact.dom_facts[0] else {
                panic!("bound fact");
            };
            let subject = match bound {
                AtomicFact::GreaterEqualFact(fact) => fact.left.clone(),
                AtomicFact::LessEqualFact(fact) => fact.left.clone(),
                _ => panic!("weak bound"),
            };
            let env = forall.local_env.clone();
            compiler.runtime.execution_environments_stack.push(env);
            let actual = if positive {
                compiler.runtime.known_positive_lower_bound_cite(&subject)
            } else {
                compiler.runtime.known_negative_upper_bound_cite(&subject)
            };
            compiler.runtime.execution_environments_stack.pop();
            assert_eq!(actual, Some(expected));
            compiler.compile_run(&run, "stable_bound").unwrap();
        }
    }
}
