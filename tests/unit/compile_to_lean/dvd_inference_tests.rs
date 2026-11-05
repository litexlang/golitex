use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferDvdFactResult, InferResult};

const SOURCE: &str = r#"forall a,b Z:
    b!=0
    $dvd(a,b)
    =>:
        a%b=0
        exist k Z st {a=k*b}
"#;

#[test]
fn dvd_definition_replays_both_original_stores_and_only_published_modulo() {
    let (mut run, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let source = &forall.assumed_dom_facts[1].store_and_infer;
    let Some(InferResult::AtomicFact(infer @ InferAtomicFactResult::DvdFact(rules))) =
        &source.infer
    else {
        panic!("original Dvd inference")
    };
    let InferDvdFactResult::Definition(p) = &rules[0];
    let StoreFactResult::AtomicFact(seed) = &source.store else {
        panic!()
    };
    let seed = Fact::AtomicFact(seed.fact.clone());
    let StoreFactResult::AtomicFact(stored) = &p.remainder_zero.store else {
        panic!()
    };
    let AtomicFact::EqualFact(eq) = &stored.fact else {
        panic!()
    };
    let remainder = p.remainder_zero.primary_fact_id();
    let multiple = p.integer_multiple.primary_fact_id();
    // The enclosing original local environment identifies subjects; its zero
    // prefix exposes no producers. Each inference cursor controls publication.
    let context = SourcePosition::new(None, SourceOwner::Forall(forall), 0);
    for before in 0..=2 {
        let position = SourcePosition::new(
            Some(&context),
            SourceOwner::AtomicInference(&seed, infer),
            before,
        );
        assert_eq!(
            position
                .dvd_remainder_subject(&p.remainder_zero.store)
                .is_some(),
            before >= 1
        );
        let visible = position
            .with_visible_inferred_subject_filter(&eq.left, &mut |store, producer| {
                Ok(producer.dvd_remainder_subject(store).map(|_| ()))
            })
            .unwrap();
        assert_eq!(visible.is_some(), before >= 1);
        assert_eq!(
            position.visible_fact(remainder, &compiler.runtime).is_ok(),
            before >= 1
        );
        assert_eq!(
            position.visible_fact(multiple, &compiler.runtime).is_ok(),
            before >= 2
        );
        let published =
            SourcePosition::new(Some(&context), SourceOwner::PropInference(source), before);
        assert_eq!(
            published
                .dvd_remainder_subject(&p.remainder_zero.store)
                .is_some(),
            before >= 1
        );
        let visible = published
            .with_visible_inferred_subject_filter(&eq.left, &mut |store, producer| {
                Ok(producer.dvd_remainder_subject(store).map(|_| ()))
            })
            .unwrap();
        assert_eq!(visible.is_some(), before >= 1);
    }
    let output = compiler
        .compile_run(&run, "dvd_inference")
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(output.matches(&format!("h_{}", remainder.value())).count() >= 2);
    assert!(output.contains(&format!("h_{}", multiple.value())));
    // The source verifier may select its existing automatic zero-remainder
    // existential rule before stored-exist lookup. The second original store
    // must still be proved and published at exactly its own stage above.
    let (declaration, _) = output.split_once(":=\n").expect("theorem declaration");
    assert!(
        !declaration.contains("_dvd_remainder_h"),
        "a theorem type cannot reference its proof-local constructor alias"
    );
    for law in ["dvdConstructorWD", "dvdRemainderZero", "dvdIntegerMultiple"] {
        assert!(output.contains(&format!("Litex.{law}")));
    }
    assert!(
        !output.contains(&format!("_dvd_remainder_h{} (M := M)", remainder.value())),
        "local constructor aliases have no parameters"
    );
    assert_eq!(output, compiler.compile_run(&run, "dvd_inference").unwrap());
    let (run, compiler) = super::execute(
        r#"$dvd(6*10,3)
"#,
    );
    compiler.compile_run(&run, "dvd_top_level").unwrap();
}

#[test]
fn dvd_inference_rejects_changed_seed_remainder_binder_and_missing_publication() {
    for change in ["seed", "remainder", "binder", "missing", "identity"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::DvdFact(rules))) =
            &mut forall.assumed_dom_facts[1].store_and_infer.infer
        else {
            panic!()
        };
        if change == "missing" {
            rules.clear();
        } else {
            let InferDvdFactResult::Definition(p) = &mut rules[0];
            match change {
                "seed" => p.source_fact_id = FactId::new(u64::MAX),
                "remainder" => {
                    let StoreFactResult::AtomicFact(stored) = &mut p.remainder_zero.store else {
                        panic!()
                    };
                    let AtomicFact::EqualFact(eq) = &mut stored.fact else {
                        panic!()
                    };
                    eq.right = Obj::Literal(Literal::Number(Number::new("1".into())));
                }
                "binder" => {
                    let StoreFactResult::ExistShapedFact(stored) = &mut p.integer_multiple.store
                    else {
                        panic!()
                    };
                    let ExistShapedFact::Exist(f) = &mut stored.fact else {
                        panic!()
                    };
                    f.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
                }
                "identity" => {
                    let StoreFactResult::ExistShapedFact(stored) = &mut p.integer_multiple.store
                    else {
                        panic!()
                    };
                    let ExistShapedFact::Exist(f) = &mut stored.fact else {
                        panic!()
                    };
                    f.fact_id = p.remainder_zero.primary_fact_id();
                    stored.whole_fact_id = f.fact_id;
                }
                _ => unreachable!(),
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "original source identity, operands, binder and ordered publications are mandatory",
        );
    }
}

#[test]
fn expanded_dvd_domain_replays_all_three_original_requirements() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for change in ["none", "missing", "order", "nonzero_subject", "carrier"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut forall.assumed_dom_facts[1].well_defined
        else {
            panic!()
        };
        let PredicateDomainProof::ByRequirements(reqs) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("original expanded domain")
        };
        assert_eq!(reqs.len(), 3);
        match change {
            "none" => {}
            "missing" => {
                reqs.pop();
            }
            "order" => reqs.swap(0, 1),
            "nonzero_subject" => {
                let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut reqs[2].requirement else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
            "carrier" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut reqs[1].requirement else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            _ => unreachable!(),
        }
        let output = compiler.compile_run(&run, change);
        if change == "none" {
            output.unwrap();
        } else {
            output.expect_err("the selected expanded Z/Z/nonzero domain is ordered and complete");
        }
    }
}
