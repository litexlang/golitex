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
