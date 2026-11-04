use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const SCALAR_FROM: &str =
    include_str!("../../../lean/examples/multivariable_continuous_from_definition/statement.lit");
const SCALAR_TO: &str =
    include_str!("../../../lean/examples/multivariable_continuous_to_definition/statement.lit");
const VECTOR_FROM: &str =
    include_str!("../../../lean/examples/vector_continuous_from_definition/statement.lit");
const VECTOR_TO: &str =
    include_str!("../../../lean/examples/vector_continuous_to_definition/statement.lit");

fn clause(b: &mut BuiltinThmApplication, fold: bool) -> &mut ForallFact {
    let f = if fold {
        b.requirements.last_mut().unwrap()
    } else {
        &mut b.conclusions[0]
    };
    let Fact::ForallFact(f) = f else { panic!() };
    f
}
fn inclusion(f: &mut ForallFact) -> &mut SubsetFact {
    let [ExistOrAndChainAtomicFact::ExistFact(e)] = f.then_facts.as_mut_slice() else {
        panic!()
    };
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s))] = e.facts.as_mut_slice() else {
        panic!()
    };
    s
}

#[test]
fn multivariable_continuity_replays_four_selected_bts() {
    for (source, law) in [
        (SCALAR_FROM, "scalarMultivariableContinuousAtFromDefinition"),
        (SCALAR_TO, "scalarMultivariableContinuousAtToDefinition"),
        (VECTOR_FROM, "vectorMultivariableContinuousAtFromDefinition"),
        (VECTOR_TO, "vectorMultivariableContinuousAtToDefinition"),
    ] {
        let (run, c) = super::execute(source);
        let output = c
            .compile_run(&run, "continuity")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, c.compile_run(&run, "continuity").unwrap());
    }
}

#[test]
fn multivariable_continuity_preserves_generic_dimensions() {
    for source in [
        include_str!(
            "../../../lean/examples/multivariable_continuous_from_definition_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_to_definition_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/vector_continuous_from_definition_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/vector_continuous_to_definition_generic/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "original_domain")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}

#[test]
fn multivariable_continuity_replays_definition_search_and_inferred_epsilon_control() {
    for source in [
        include_str!("../../../lean/examples/multivariable_continuous_definition/statement.lit"),
        include_str!("../../../lean/examples/multivariable_continuous_inference/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_definition/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_inference/statement.lit"),
        include_str!(
            "../../../lean/examples/multivariable_continuous_guarded_citation/statement.lit"
        ),
        include_str!("../../../lean/examples/vector_continuous_guarded_citation/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "definition_and_inference")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}

#[test]
fn multivariable_continuity_retains_every_original_schema_stage() {
    for source in [SCALAR_FROM, SCALAR_TO, VECTOR_FROM, VECTOR_TO] {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "arguments",
            "conclusion",
            "derivation",
        ] {
            let (mut run, c) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                "proof_order" => call.dom_proofs.swap(0, 1),
                "store_order" => call.dom_stores.swap(0, 1),
                "arguments" => {
                    call.builtin.as_mut().unwrap().arguments.pop();
                }
                "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    call.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(c.compile_run(&run, "bad_stages").is_err(), "{change}");
        }
    }
}

#[test]
fn multivariable_continuity_rejects_changed_epsilon_binders_carriers_and_bounds() {
    for source in [SCALAR_TO, VECTOR_TO] {
        for change in [
            "epsilon_carrier",
            "epsilon_premise",
            "epsilon_count",
            "delta_carrier",
            "delta_count",
            "delta_capture",
            "target_epsilon",
        ] {
            let (mut run, c) = super::execute(source);
            let f = clause(invocation(&mut run).builtin.as_mut().unwrap(), false);
            match change {
                "epsilon_carrier" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                "epsilon_premise" => f.dom_facts.push(Fact::ForallFact(f.clone())),
                "epsilon_count" => f.typed_parameters.groups[0].params.clear(),
                "target_epsilon" => {
                    let Obj::SetFormer(SetFormer::SetBuilder(g)) = &mut inclusion(f).right else {
                        panic!()
                    };
                    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(q)) = &mut g.facts[0]
                    else {
                        panic!()
                    };
                    q.right = super::number_object("0");
                }
                _ => {
                    let epsilon = f.typed_parameters.groups[0].params[0].id;
                    let [ExistOrAndChainAtomicFact::ExistFact(e)] = f.then_facts.as_mut_slice()
                    else {
                        panic!()
                    };
                    match change {
                        "delta_carrier" => {
                            e.typed_parameters.groups[0].param_type =
                                ParamType::Obj(Obj::StandardSet(StandardSet::R))
                        }
                        "delta_count" => e.typed_parameters.groups[0].params.clear(),
                        _ => e.typed_parameters.groups[0].params[0].id = epsilon,
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_control_binders").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn multivariable_continuity_keeps_unpunctured_neighborhood_original_domain_and_point() {
    for source in [SCALAR_TO, VECTOR_TO] {
        for change in [
            "puncture",
            "domain",
            "radius",
            "distance_dimension",
            "input_point",
            "binder_capture",
            "target_point",
            "output_dimension",
        ] {
            let (mut run, c) = super::execute(source);
            let s = inclusion(clause(
                invocation(&mut run).builtin.as_mut().unwrap(),
                false,
            ));
            let (
                Obj::SetFormer(SetFormer::SetBuilder(near)),
                Obj::SetFormer(SetFormer::SetBuilder(good)),
            ) = (&mut s.left, &mut s.right)
            else {
                panic!()
            };
            match change {
                "puncture" => near.facts.push(near.facts[0].clone()),
                "domain" => near.param_set = Box::new(Obj::StandardSet(StandardSet::R)),
                "binder_capture" => good.param_binding.id = near.param_binding.id,
                "target_point" | "output_dimension" => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(q)) =
                        &mut good.facts[0]
                    else {
                        panic!()
                    };
                    match &mut q.left {
                        Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) =
                                a.arg.as_mut()
                            else {
                                panic!()
                            };
                            s.right = Box::new(super::number_object("0"));
                        }
                        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(a)) => {
                            if change == "output_dimension" {
                                a.dimension = Box::new(super::number_object("99"));
                            } else {
                                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) =
                                    a.vector.as_mut()
                                else {
                                    panic!()
                                };
                                let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) =
                                    f.equal_to.as_mut()
                                else {
                                    panic!()
                                };
                                s.right = Box::new(super::number_object("0"));
                            }
                        }
                        _ => panic!(),
                    }
                }
                _ => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(q)) =
                        &mut near.facts[0]
                    else {
                        panic!()
                    };
                    if change == "radius" {
                        q.right = super::number_object("0");
                    } else {
                        let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(n)) = &mut q.left
                        else {
                            panic!()
                        };
                        if change == "distance_dimension" {
                            n.dimension = Box::new(super::number_object("99"));
                        } else {
                            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) =
                                n.vector.as_mut()
                            else {
                                panic!()
                            };
                            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) =
                                f.equal_to.as_mut()
                            else {
                                panic!()
                            };
                            s.right = Box::new(super::number_object("0"));
                        }
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_control_domain").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn multivariable_continuity_requires_original_inference_and_positive_predicate() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for source in [SCALAR_TO, VECTOR_TO] {
        for change in ["infer", "derived", "source", "domain", "negative"] {
            let (mut run, c) = super::execute(source);
            let call = invocation(&mut run);
            if change == "negative" {
                let b = call.builtin.as_mut().unwrap();
                let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                    b.requirements.last().unwrap()
                else {
                    panic!()
                };
                let neg = NotMultivariableAnalysisFact {
                    fact_id: f.fact_id,
                    relation: f.relation.clone(),
                    line_file: f.line_file.clone(),
                };
                *b.requirements.last_mut().unwrap() =
                    Fact::AtomicFact(AtomicFact::NotMultivariableAnalysisFact(neg));
            } else if change == "infer" {
                call.dom_stores.last_mut().unwrap().infer = None;
            } else {
                let Some(InferResult::AtomicFact(
                    InferAtomicFactResult::MultivariableAnalysisFact(rules),
                )) = &mut call.dom_stores.last_mut().unwrap().infer
                else {
                    panic!()
                };
                let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    "derived" => p.derived.clear(),
                    "source" => p.source_fact_id = FactId::new(u64::MAX),
                    _ => p.function_domain = None,
                }
            }
            assert!(c.compile_run(&run, "bad_inference").is_err(), "{change}");
        }
    }
}

#[test]
fn multivariable_continuity_rejects_future_epsilon_clause_citations() {
    for source in [SCALAR_FROM, VECTOR_FROM] {
        let (mut run, c) = super::execute(source);
        let call = invocation(&mut run);
        let future = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(f) = call.dom_proofs.last_mut().unwrap() else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) =
            f.as_mut()
        else {
            panic!("original forall citation")
        };
        f.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_clause").is_err());
    }
}

#[test]
fn multivariable_continuity_definition_retains_clause_proof_and_source_scope() {
    use crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition, BuiltinPropDefinitionProof,
    };
    for source in [
        include_str!("../../../lean/examples/multivariable_continuous_definition/statement.lit"),
        include_str!("../../../lean/examples/vector_continuous_definition/statement.lit"),
    ] {
        for change in ["missing", "epsilon_carrier", "future"] {
            let (mut run, c) = super::execute(source);
            let root = super::forall_proof_mut(&mut run.statement_results[0]);
            let future = root.proved_then_facts[0].store_and_infer.primary_fact_id();
            let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByDefinition(
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::MultivariableAnalysis(p),
                ),
            ) = &mut atomic.searched_proof
            else {
                panic!("original definition search")
            };
            let (requirements, proofs) = match p {
                MultivariableDefinitionProof::ScalarContinuousAt(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                MultivariableDefinitionProof::VectorContinuousAt(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                _ => panic!("continuity"),
            };
            match change {
                "missing" => proofs.clear(),
                "epsilon_carrier" => {
                    let Fact::ForallFact(f) = &mut requirements[0] else {
                        panic!()
                    };
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R));
                }
                _ => {
                    let VerifyFactResult::ForallFact(p) = &mut proofs[0] else {
                        panic!()
                    };
                    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                        p,
                    )) = p.as_mut()
                    else {
                        panic!("original epsilon citation")
                    };
                    p.cite_fact_id = future;
                }
            }
            assert!(
                c.compile_run(&run, "bad_definition_capture").is_err(),
                "{change}"
            );
        }
    }
}
