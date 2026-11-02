use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferPrimeFactResult, InferResult};

const SOURCE: &str = include_str!("../../../lean/examples/prime_definition_replay/statement.lit");

#[test]
fn prime_definition_publishes_both_original_stores_and_their_carrier() {
    let (mut run, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let store = &forall.assumed_dom_facts[0].store_and_infer;
    let Some(InferResult::AtomicFact(infer @ InferAtomicFactResult::PrimeFact(rules))) =
        &store.infer
    else {
        panic!("prime inference")
    };
    let InferPrimeFactResult::Definition(p) = &rules[0];
    let lower = p.lower_bound.primary_fact_id();
    let trial = p.trial_divisors.primary_fact_id();
    let StoreFactResult::AtomicFact(seed) = &store.store else {
        panic!()
    };
    let seed = Fact::AtomicFact(seed.fact.clone());
    let StoreFactResult::ForallFact(stored) = &p.trial_divisors.store else {
        panic!()
    };
    let ParamType::Obj(carrier) = &stored.fact.typed_parameters.groups[0].param_type else {
        panic!()
    };
    for before in 0..=2 {
        let position =
            SourcePosition::new(None, SourceOwner::AtomicInference(&seed, infer), before);
        assert_eq!(
            position
                .prime_trial_carrier(&p.trial_divisors.store)
                .is_some(),
            before == 2
        );
        let visible = position
            .with_visible_inferred_subject_filter(carrier, &mut |store, producer| {
                compiler.compile_prime_inferred_subject(carrier, store, producer)
            })
            .unwrap();
        assert_eq!(
            visible.is_some(),
            before == 2,
            "trial carrier cannot escape its original publication stage"
        );
    }
    let output = compiler
        .compile_run(&run, "prime_inferences")
        .unwrap_or_else(|e| panic!("{e}"));
    for id in [lower, trial] {
        assert!(output.matches(&format!("h_{}", id.value())).count() >= 2);
    }
    assert!(output.contains("Litex.primeLowerBound"));
    assert!(output.contains("Litex.primeTrialDivisors"));
    assert!(output.contains("_prime_trial_range_h"));
    assert!(
        !output.contains(&format!("_prime_trial_range_h{} (M := M)", trial.value())),
        "the original locally bound range is a let, so it has no model parameter"
    );
}

#[test]
fn prime_inference_rejects_changed_seed_lower_trial_and_missing_publication() {
    for change in ["seed", "lower", "trial", "missing"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::PrimeFact(rules))) =
            &mut forall.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!()
        };
        if change == "missing" {
            rules.clear();
        } else {
            let InferPrimeFactResult::Definition(p) = &mut rules[0];
            match change {
                "seed" => p.source_fact_id = FactId::new(u64::MAX),
                "lower" => {
                    let StoreFactResult::AtomicFact(stored) = &mut p.lower_bound.store else {
                        panic!()
                    };
                    let AtomicFact::LessEqualFact(f) = &mut stored.fact else {
                        panic!()
                    };
                    f.left = Obj::Literal(Literal::Number(Number::new("1".into())));
                }
                "trial" => {
                    let StoreFactResult::ForallFact(stored) = &mut p.trial_divisors.store else {
                        panic!()
                    };
                    stored.fact.typed_parameters.groups[0].params[0].id =
                        IdentifierId::new(u64::MAX);
                }
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain original prime definition producers and subject identities");
    }
}

#[test]
fn prime_trial_application_keeps_original_mod_children_and_formation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
    for change in ["missing", "order", "constructor", "formation"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[1].verify_result);
        if change == "formation" {
            proof
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(application) =
                &mut proof.searched_proof
            else {
                panic!("original prime trial application")
            };
            let captured = &mut application.as_detailed_mut().unwrap().arg_match_proofs[0];
            let DetailedForallConclusionArgMatchProof::ByStructure {
                pattern,
                child_matches,
                ..
            } = captured.as_detailed_mut().unwrap()
            else {
                panic!("original mod structural match")
            };
            match change {
                "missing" => {
                    child_matches.pop();
                }
                "order" => child_matches.swap(0, 1),
                "constructor" => {
                    let Obj::IntegerOperator(IntegerOperator::Mod(m)) = pattern else {
                        panic!()
                    };
                    *pattern = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                        left: m.left.clone(),
                        right: m.right.clone(),
                    }));
                }
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original modulo constructor, child matches and scoped WD are mandatory");
    }
}
