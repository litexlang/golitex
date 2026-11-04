use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 4] = [
    include_str!("../../../lean/examples/vector_limit_add/statement.lit"),
    include_str!("../../../lean/examples/vector_limit_subtract/statement.lit"),
    include_str!("../../../lean/examples/vector_continuous_add/statement.lit"),
    include_str!("../../../lean/examples/vector_continuous_subtract/statement.lit"),
];
#[test]
fn euclidean_vector_algebra_cached_formation_requires_exact_visible_source_and_argument_proofs() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    let source =
        include_str!("../../../lean/examples/vector_continuous_subtract_aliased/statement.lit");
    for change in ["future", "missing", "equalities", "wrong_family"] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let builtin = p.builtin.as_ref().unwrap();
        let future = builtin.conclusions[0].fact_id();
        let wrong = builtin.requirements[0].fact_id();
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
            panic!()
        };
        let PredicateDomainProof::ByKnownFact(cite) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("actual source must select cached formation")
        };
        match change {
            "future" => cite.cite_fact_id = future,
            "missing" => cite.cite_fact_id = FactId::new(u64::MAX),
            "equalities" => {
                cite.why_parameters_of_known_fact_are_equal_to_givens.pop();
            }
            _ => cite.cite_fact_id = wrong,
        }
        assert!(
            c.compile_run(&run, "bad_cached_formation").is_err(),
            "{change}"
        );
    }
}
fn literal(obj: &mut Obj) -> &mut AnonymousFn {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = obj else {
        panic!()
    };
    f
}
fn mutate_formula(obj: &mut Obj, change: &str) {
    let f = literal(obj);
    match change {
        "carrier" => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
        "index" => {
            f.body.set_bound_parameters.groups[0].param_type =
                Box::new(Obj::StandardSet(StandardSet::R))
        }
        "guard" => {
            f.body
                .dom_facts
                .push(QuantifierFreeFact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: FactId::new(u64::MAX),
                    element: super::number_object("0"),
                    set: Obj::StandardSet(StandardSet::R),
                    line_file: None,
                })));
        }
        "binder" => f.body.set_bound_parameters.groups[0].params.clear(),
        _ => {
            use crate::rational_expression::helper::{add_objs, sub_objs};
            let new = match f.equal_to.as_ref() {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
                    if change == "operation" {
                        sub_objs((*x.left).clone(), (*x.right).clone())
                    } else if change == "operand" {
                        add_objs((*x.left).clone(), super::number_object("0"))
                    } else {
                        add_objs((*x.right).clone(), (*x.left).clone())
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
                    if change == "operation" {
                        add_objs((*x.left).clone(), (*x.right).clone())
                    } else if change == "operand" {
                        sub_objs((*x.left).clone(), super::number_object("0"))
                    } else {
                        sub_objs((*x.right).clone(), (*x.left).clone())
                    }
                }
                _ => panic!(),
            };
            f.equal_to = Box::new(new);
        }
    }
}
#[test]
fn euclidean_vector_algebra_replays_four_original_schemas_deterministically() {
    for (i, source) in SOURCES.iter().enumerate() {
        let (run, c) = super::execute(source);
        let out = c
            .compile_run(&run, "vector_algebra")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains(&format!(
            "Litex.vectorMultivariable{}{}",
            if i < 2 { "Limit" } else { "Continuous" },
            if i % 2 == 0 { "Add" } else { "Subtract" }
        )));
        assert!(out.contains("_vector_algebra_formula"));
        assert_eq!(out, c.compile_run(&run, "vector_algebra").unwrap());
    }
}
#[test]
fn euclidean_vector_algebra_preserves_ordered_proofs_stores_wd_and_selected_identity() {
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
fn euclidean_vector_algebra_retains_complete_coordinate_formula() {
    for (i, source) in SOURCES.iter().enumerate() {
        for change in [
            "carrier",
            "index",
            "guard",
            "binder",
            "operation",
            "operand",
            "order",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let index = 3 * if i < 2 { 5 } else { 6 } + 2;
            let Fact::ForallFact(all) = &mut p.builtin.as_mut().unwrap().requirements[index] else {
                panic!()
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                &mut all.then_facts[0]
            else {
                panic!()
            };
            mutate_formula(&mut eq.right, change);
            assert!(c.compile_run(&run, "bad_coordinates").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_vector_algebra_retains_result_dimensions_point_and_coordinate_formula() {
    for (i, source) in SOURCES.iter().enumerate() {
        let changes = if i < 2 {
            vec![
                "point",
                "input",
                "output",
                "carrier",
                "index",
                "guard",
                "binder",
                "operation",
                "operand",
                "order",
            ]
        } else {
            vec!["point", "input", "output"]
        };
        for change in changes {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!()
            };
            match &mut f.relation {
                MultivariableAnalysisRelation::VectorLimit(r) => match change {
                    "point" => r.point = super::number_object("99"),
                    "input" => r.input_dimension = super::number_object("99"),
                    "output" => r.output_dimension = super::number_object("99"),
                    _ => mutate_formula(&mut r.value, change),
                },
                MultivariableAnalysisRelation::VectorContinuousAt(r) => match change {
                    "point" => r.point = super::number_object("99"),
                    "input" => r.input_dimension = super::number_object("99"),
                    _ => r.output_dimension = super::number_object("99"),
                },
                _ => panic!(),
            }
            assert!(c.compile_run(&run, "bad_result").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_vector_algebra_requires_outer_formula_domain_subject_and_capture() {
    for (i, source) in SOURCES.iter().enumerate() {
        for change in ["domain", "subject", "orientation", "binder"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let b = p.builtin.as_mut().unwrap();
            let index = 3 * if i < 2 { 5 } else { 6 } + 2;
            let Fact::ForallFact(all) = &mut b.requirements[index] else {
                panic!()
            };
            if change == "domain" {
                all.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else if change == "binder" {
                all.typed_parameters.groups[0].params.clear();
            } else {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut all.then_facts[0]
                else {
                    panic!()
                };
                if change == "subject" {
                    eq.left = super::number_object("0");
                } else {
                    std::mem::swap(&mut eq.left, &mut eq.right);
                }
            }
            assert!(c.compile_run(&run, "bad_outer").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_vector_algebra_requires_original_candidate_inference_and_complete_domain() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for (i, source) in SOURCES.iter().enumerate() {
        for which in [0, 1] {
            for change in ["missing", "source", "derived", "domain"] {
                let (mut run, c) = super::execute(source);
                let p = invocation(&mut run);
                let infer = &mut p.dom_stores[3 * if i < 2 { 5 } else { 6 } + which].infer;
                if change == "missing" {
                    *infer = None;
                } else {
                    let Some(InferResult::AtomicFact(
                        InferAtomicFactResult::MultivariableAnalysisFact(rules),
                    )) = infer
                    else {
                        panic!()
                    };
                    let [InferMultivariableAnalysisFactResult::Definition(d)] =
                        rules.as_mut_slice()
                    else {
                        panic!()
                    };
                    match change {
                        "source" => d.source_fact_id = FactId::new(u64::MAX),
                        "derived" => d.derived.clear(),
                        _ => d.function_domain = None,
                    }
                }
                assert!(
                    c.compile_run(&run, "bad_inference").is_err(),
                    "{which} /{change}"
                );
            }
        }
    }
}
#[test]
fn euclidean_vector_algebra_rejects_future_formula_citation() {
    for (i, source) in SOURCES.iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(f) = &mut p.dom_proofs[3 * if i < 2 { 5 } else { 6 } + 2]
        else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) =
            f.as_mut()
        else {
            panic!()
        };
        f.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_formula").is_err());
    }
}
#[test]
fn euclidean_vector_algebra_requires_original_output_context_and_value_formation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in SOURCES {
        for change in ["count", "dimension", "domain"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let PredicateDomainProof::MultivariableAnalysis(f) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!()
            };
            if change == "count" {
                f.requirements.pop();
            } else if change == "domain" {
                f.function_domain.signature.dom_facts.clear();
                f.function_domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
            } else {
                let Fact::AtomicFact(AtomicFact::InFact(d)) = &mut f.requirements[2].requirement
                else {
                    panic!()
                };
                d.element = super::number_object("99");
            }
            assert!(c.compile_run(&run, "bad_output").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_vector_algebra_preserves_generic_guarded_and_aliased_functions() {
    for source in [
        include_str!("../../../lean/examples/vector_limit_add_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_subtract_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_add_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_subtract_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_add_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_subtract_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_add_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_subtract_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_limit_add_aliased/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_subtract_aliased/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "actual_domains")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
