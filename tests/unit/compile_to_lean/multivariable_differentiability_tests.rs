use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const SCALAR_FROM: &str = include_str!(
    "../../../lean/examples/multivariable_differentiable_from_definition/statement.lit"
);
const SCALAR_TO: &str =
    include_str!("../../../lean/examples/multivariable_differentiable_to_definition/statement.lit");
const VECTOR_FROM: &str =
    include_str!("../../../lean/examples/vector_differentiable_from_definition/statement.lit");
const VECTOR_TO: &str =
    include_str!("../../../lean/examples/vector_differentiable_to_definition/statement.lit");

fn existential(b: &mut BuiltinThmApplication, fold: bool) -> &mut PlainExistFact {
    let f = if fold {
        b.requirements.last_mut().unwrap()
    } else {
        &mut b.conclusions[0]
    };
    let Fact::ExistFact(e) = f else { panic!() };
    e
}

#[test]
fn multivariable_differentiability_replays_four_definition_bts() {
    for (source, law) in [
        (SCALAR_FROM, "scalarDifferentiableAtFromDefinition"),
        (SCALAR_TO, "scalarDifferentiableAtToDefinition"),
        (VECTOR_FROM, "vectorDifferentiableAtFromDefinition"),
        (VECTOR_TO, "vectorDifferentiableAtToDefinition"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "differentiability")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "differentiability").unwrap()
        );
    }
}

#[test]
fn multivariable_differentiability_replays_generic_and_guarded_domains() {
    for source in [
        include_str!("../../../lean/examples/multivariable_differentiable_from_definition_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_differentiable_to_definition_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_differentiable_from_definition_generic/statement.lit"),
        include_str!("../../../lean/examples/vector_differentiable_to_definition_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_differentiable_from_definition_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_differentiable_to_definition_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_differentiable_from_definition_guarded/statement.lit"),
        include_str!("../../../lean/examples/vector_differentiable_to_definition_guarded/statement.lit"),
    ] {
        let (run,compiler)=super::execute(source);
        compiler.compile_run(&run,"dimension_domain").unwrap_or_else(|e|panic!("{source}: {e}"));
    }
}

#[test]
fn multivariable_differentiability_retains_original_ordered_stages() {
    for source in [SCALAR_FROM, SCALAR_TO, VECTOR_FROM, VECTOR_TO] {
        for change in [
            "proof",
            "store",
            "wd",
            "order",
            "stores",
            "arguments",
            "conclusion",
            "identity",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                "order" => call.dom_proofs.swap(0, 1),
                "stores" => call.dom_stores.swap(0, 1),
                "arguments" => {
                    call.builtin.as_mut().unwrap().arguments.pop();
                }
                "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut call.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
            }
            assert!(
                compiler.compile_run(&run, "bad_stages").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn multivariable_differentiability_retains_exact_matrix_witness_contract() {
    for (source, fold) in [
        (SCALAR_FROM, true),
        (SCALAR_TO, false),
        (VECTOR_FROM, true),
        (VECTOR_TO, false),
    ] {
        for change in [
            "carrier",
            "rows",
            "cols",
            "binders",
            "candidate",
            "negative",
            "capture",
        ] {
            let (mut run, compiler) = super::execute(source);
            let e = existential(invocation(&mut run).builtin.as_mut().unwrap(), fold);
            match change {
                "binders" => e.typed_parameters.groups[0].params.clear(),
                "capture" => {
                    let id = e.typed_parameters.groups[0].params[0].id;
                    let [QuantifierFreeFact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f))] =
                        e.facts.as_mut_slice()
                    else {
                        panic!()
                    };
                    let mut args: Vec<_> =
                        f.relation.argument_refs().into_iter().cloned().collect();
                    args[0] = Obj::Identifier(IdentifierObj::Plain {
                        id,
                        name: "captured".into(),
                    });
                    f.relation = f.relation.with_arguments(&args);
                }
                "candidate" => e.facts.clear(),
                "negative" => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                        &e.facts[0]
                    else {
                        panic!()
                    };
                    e.facts[0] = QuantifierFreeFact::AtomicFact(
                        AtomicFact::NotMultivariableAnalysisFact(NotMultivariableAnalysisFact {
                            fact_id: f.fact_id,
                            relation: f.relation.clone(),
                            line_file: f.line_file.clone(),
                        }),
                    );
                }
                _ => {
                    let ParamType::Obj(Obj::SetFormer(SetFormer::MatrixSet(m))) =
                        &mut e.typed_parameters.groups[0].param_type
                    else {
                        panic!()
                    };
                    match change {
                        "carrier" => m.set = Box::new(Obj::StandardSet(StandardSet::C)),
                        "rows" => m.rows = Box::new(super::number_object("77")),
                        _ => m.cols = Box::new(super::number_object("77")),
                    }
                }
            }
            assert!(
                compiler.compile_run(&run, "bad_witness").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn multivariable_differentiability_retains_native_schema_and_inference_capture() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for source in [SCALAR_TO, VECTOR_TO] {
        for change in ["derivation", "inference", "derived", "source", "domain"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            if change == "derivation" {
                call.theorem_derivation = TheoremDerivationProof::UserTheorem;
            } else if change == "inference" {
                call.dom_stores.last_mut().unwrap().infer = None;
            } else {
                let Some(InferResult::AtomicFact(
                    InferAtomicFactResult::MultivariableAnalysisFact(rules),
                )) = &mut call.dom_stores.last_mut().unwrap().infer
                else {
                    panic!()
                };
                let [InferMultivariableAnalysisFactResult::Definition(c)] = rules.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    "derived" => c.derived.clear(),
                    "source" => c.source_fact_id = FactId::new(u64::MAX),
                    _ => c.function_domain = None,
                }
            }
            assert!(
                compiler.compile_run(&run, "bad_inference").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn multivariable_differentiability_replays_definition_search_and_inferred_selectors() {
    for source in [
        include_str!(
            "../../../lean/examples/multivariable_differentiable_definition/statement.lit"
        ),
        include_str!("../../../lean/examples/vector_differentiable_definition/statement.lit"),
        include_str!(
            "../../../lean/examples/multivariable_differentiable_definition_guarded/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/vector_differentiable_definition_guarded/statement.lit"
        ),
        include_str!("../../../lean/examples/multivariable_differentiable_selector/statement.lit"),
        include_str!("../../../lean/examples/vector_differentiable_selector/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "actual_search_inference")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}

#[test]
fn multivariable_differentiability_rejects_future_existential_citation() {
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
    for source in [SCALAR_FROM, VECTOR_FROM] {
        let (mut run, c) = super::execute(source);
        let call = invocation(&mut run);
        let future = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let proof = call.dom_proofs.last_mut().unwrap();
        let VerifyFactResult::ExistShapedFact(p) = proof else {
            panic!("existence")
        };
        let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
            p.as_mut()
        else {
            panic!("success")
        };
        let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) = &mut p.searched_proof
        else {
            panic!("original existential citation")
        };
        cite.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_exists").is_err());
    }
}

#[test]
fn multivariable_differentiability_definition_retains_existential_proof_and_scope() {
    use crate::execute::execute_fact_stmt::multivariable::definition::MultivariableDefinitionProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition, BuiltinPropDefinitionProof,
    };
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
    for source in [
        include_str!(
            "../../../lean/examples/multivariable_differentiable_definition/statement.lit"
        ),
        include_str!("../../../lean/examples/vector_differentiable_definition/statement.lit"),
    ] {
        for change in ["missing", "carrier", "future"] {
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
                MultivariableDefinitionProof::ScalarDifferentiableAt(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                MultivariableDefinitionProof::TotalDifferentiableAt(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                _ => panic!("differentiability"),
            };
            match change {
                "missing" => proofs.clear(),
                "carrier" => {
                    let Fact::ExistFact(e) = &mut requirements[0] else {
                        panic!()
                    };
                    e.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C));
                }
                _ => {
                    let VerifyFactResult::ExistShapedFact(p) = &mut proofs[0] else {
                        panic!()
                    };
                    let VerifyExistShapedFactResult::PlainExistFact(
                        VerifyPlainExistFactResult::Success(p),
                    ) = p.as_mut()
                    else {
                        panic!()
                    };
                    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) =
                        &mut p.searched_proof
                    else {
                        panic!()
                    };
                    cite.cite_fact_id = future;
                }
            }
            assert!(
                c.compile_run(&run, "bad_definition_capture").is_err(),
                "{change}"
            );
        }
    }
}
