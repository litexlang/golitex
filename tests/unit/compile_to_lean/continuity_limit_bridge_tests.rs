use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const SOURCES: [&str; 4] = [
    include_str!("../../../lean/examples/multivariable_continuity_to_limit/statement.lit"),
    include_str!("../../../lean/examples/multivariable_limit_to_continuity/statement.lit"),
    include_str!("../../../lean/examples/vector_continuity_to_limit/statement.lit"),
    include_str!("../../../lean/examples/vector_limit_to_continuity/statement.lit"),
];

#[test]
fn continuity_limit_bridge_replays_four_selected_rules_deterministically() {
    for (source, law) in SOURCES.iter().zip([
        "scalarContinuityToMultivariableLimit",
        "scalarMultivariableLimitToContinuity",
        "vectorContinuityToMultivariableLimit",
        "vectorMultivariableLimitToContinuity",
    ]) {
        let (run, c) = super::execute(source);
        let output = c
            .compile_run(&run, "bridge")
            .unwrap_or_else(|e| panic!("{law}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, c.compile_run(&run, "bridge").unwrap());
    }
}

#[test]
fn continuity_limit_bridge_retains_ordered_proofs_stores_and_formation() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "args",
            "result",
            "route",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store_order" => p.dom_stores.swap(0, 1),
                "args" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "result" => p.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(c.compile_run(&run, "bad_stages").is_err(), "{change}");
        }
    }
}

#[test]
fn continuity_limit_bridge_requires_independent_punctured_accumulation() {
    for source in [SOURCES[0], SOURCES[2]] {
        for change in [
            "radius_carrier",
            "premise",
            "domain",
            "puncture",
            "radius",
            "dimension",
            "capture",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::ForallFact(all) = p.requirements.last_mut().unwrap() else {
                panic!()
            };
            if change == "radius_carrier" {
                all.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else if change == "premise" {
                all.dom_facts.push(Fact::ForallFact(all.clone()));
            } else {
                let radius = all.typed_parameters.groups[0].params[0].id;
                let [ExistOrAndChainAtomicFact::ExistFact(e)] = all.then_facts.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    "domain" => {
                        e.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::R))
                    }
                    "capture" => e.typed_parameters.groups[0].params[0].id = radius,
                    "puncture" => {
                        e.facts.remove(0);
                    }
                    _ => {
                        let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(f)) =
                            &mut e.facts[1]
                        else {
                            panic!()
                        };
                        if change == "radius" {
                            f.right = super::number_object("0");
                        } else {
                            let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(n)) = &mut f.left
                            else {
                                panic!()
                            };
                            n.dimension = Box::new(super::number_object("99"));
                        }
                    }
                }
            }
            assert!(c.compile_run(&run, "bad_accumulation").is_err(), "{change}");
        }
    }
}

#[test]
fn continuity_limit_bridge_requires_point_domain_and_original_value_equality() {
    for source in [SOURCES[1], SOURCES[3]] {
        for change in ["domain", "point", "orientation", "value"] {
            let (mut run, c) = super::execute(source);
            let req = &mut invocation(&mut run).builtin.as_mut().unwrap().requirements;
            let count = req.len();
            if change == "domain" || change == "point" {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req[count - 2] else {
                    panic!()
                };
                if change == "domain" {
                    f.set = Obj::StandardSet(StandardSet::R);
                } else {
                    f.element = super::number_object("0");
                }
            } else {
                let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut req[count - 1] else {
                    panic!()
                };
                if change == "orientation" {
                    std::mem::swap(&mut f.left, &mut f.right);
                } else {
                    f.right = super::number_object("0");
                }
            }
            assert!(c.compile_run(&run, "bad_point_value").is_err(), "{change}");
        }
    }
}

#[test]
fn continuity_limit_bridge_requires_original_candidate_inference() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for (i, source) in SOURCES.iter().enumerate() {
        for change in ["missing", "source", "derived", "domain"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let index = p.dom_stores.len() - if i % 2 == 0 { 2 } else { 3 };
            let infer = &mut p.dom_stores[index].infer;
            if change == "missing" {
                *infer = None;
            } else {
                let Some(InferResult::AtomicFact(
                    InferAtomicFactResult::MultivariableAnalysisFact(rules),
                )) = infer
                else {
                    panic!()
                };
                let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    "source" => p.source_fact_id = FactId::new(u64::MAX),
                    "derived" => p.derived.clear(),
                    _ => p.function_domain = None,
                }
            }
            assert!(
                c.compile_run(&run, "bad_candidate_inference").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn continuity_limit_bridge_rejects_future_accumulation_citation() {
    for source in [SOURCES[0], SOURCES[2]] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(f) = p.dom_proofs.last_mut().unwrap() else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) =
            f.as_mut()
        else {
            panic!("forall citation")
        };
        f.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_accumulation").is_err());
    }
}

#[test]
fn continuity_limit_bridge_preserves_generic_guarded_and_reversed_source_equalities() {
    for source in [
        include_str!("../../../lean/examples/multivariable_continuity_to_limit_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_to_continuity_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_continuity_to_limit_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_to_continuity_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_to_continuity_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_to_continuity_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_to_continuity_reversed_equality/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_to_continuity_reversed_equality/statement.lit"),
    ] {
        let (run,c)=super::execute(source);
        c.compile_run(&run,"original_domains").unwrap_or_else(|e|panic!("{source}: {e}"));
    }
}

#[test]
fn continuity_limit_bridge_requires_exact_result_and_its_wd_requirements() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in SOURCES {
        for change in [
            "result_args",
            "formation_count",
            "formation_context",
            "formation_value",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if change == "result_args" {
                let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                match &mut f.relation {
                    MultivariableAnalysisRelation::ScalarLimit(r) => {
                        r.value = super::number_object("99")
                    }
                    MultivariableAnalysisRelation::VectorLimit(r) => {
                        r.value = super::number_object("99")
                    }
                    MultivariableAnalysisRelation::ScalarContinuousAt(r) => {
                        r.point = super::number_object("99")
                    }
                    MultivariableAnalysisRelation::VectorContinuousAt(r) => {
                        r.point = super::number_object("99")
                    }
                    _ => panic!(),
                }
            } else {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                let PredicateDomainProof::MultivariableAnalysis(capture) =
                    &mut wd.as_detailed_mut().unwrap().predicate_domain
                else {
                    panic!()
                };
                if change == "formation_count" {
                    capture.requirements.pop();
                } else {
                    let index = if change == "formation_context" {
                        0
                    } else {
                        capture.requirements.len() - 1
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut capture.requirements[index].requirement
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
            }
            assert!(
                c.compile_run(&run, "bad_result_formation").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn continuity_limit_bridge_replays_selected_limit_after_candidate_storage() {
    for source in [
        include_str!(
            "../../../lean/examples/multivariable_continuity_to_limit_selector/statement.lit"
        ),
        include_str!("../../../lean/examples/vector_continuity_to_limit_selector/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        let output = c
            .compile_run(&run, "stored_limit")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains("ContinuityToMultivariableLimit"));
        assert!(output.contains("LimitEqCandidate"));
    }
}
