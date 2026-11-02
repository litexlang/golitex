use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
const FIXED: &str =
    include_str!("../../../lean/examples/multivariable_limit_builtin_definition/statement.lit");
const GENERIC: &str = include_str!(
    "../../../lean/examples/multivariable_limit_generic_builtin_definition/statement.lit"
);
#[test]
fn multivariable_definition_replays_original_complete_domain_and_both_clauses() {
    for source in [FIXED, GENERIC] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "multi_definition").unwrap();
        assert!(output.contains("Litex.multivariableScalarLimitOfClauses"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "multi_definition").unwrap()
        );
    }
}
#[test]
fn multivariable_definition_preserves_all_six_proof_store_and_formation_stages() {
    for change in [
        "args",
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "nested_wd",
        "types",
    ] {
        let (mut run, compiler) = super::execute(FIXED);
        let p = invocation(&mut run);
        match change {
            "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(4, 5),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(4, 5),
            "wd" => p.conclusions_wd.clear(),
            "nested_wd" => {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                wd.as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .clear();
            }
            _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
        }
        compiler.compile_run(&run, change).expect_err(
            "a definition theorem must preserve the original domain, both clauses and WD",
        );
    }
}
#[test]
fn multivariable_definition_requires_original_context_complete_signature_and_value() {
    for change in ["context", "signature", "dimension", "value"] {
        let (mut run, compiler) = super::execute(FIXED);
        let p = invocation(&mut run);
        if change == "signature" {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!()
            };
            capture.function_domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else if change == "context" {
            let Fact::AtomicFact(AtomicFact::InFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[0]
            else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::N);
        } else {
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!()
            };
            let MultivariableAnalysisRelation::ScalarLimit(r) = &mut f.relation else {
                panic!()
            };
            if change == "dimension" {
                r.dimension = super::number_object("3");
            } else {
                r.value = super::number_object("0");
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("context capture cannot certify another function/dimension/value");
    }
}
#[test]
fn multivariable_definition_retains_exact_positive_binders_accumulation_and_epsilon_clauses() {
    for change in [
        "accumulation",
        "epsilon",
        "positive_radius",
        "guard",
        "capture",
    ] {
        let (mut run, compiler) = super::execute(FIXED);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = p.requirements[0].clone();
        let function = p.arguments[0].clone();
        let index = if change == "epsilon" { 5 } else { 4 };
        let Fact::ForallFact(f) = &mut p.requirements[index] else {
            panic!()
        };
        match change {
            "accumulation" | "epsilon" => f.then_facts.clear(),
            "positive_radius" => {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            "guard" => f.dom_facts.push(guard),
            "capture" => {
                let Obj::Identifier(IdentifierObj::Plain { id, .. }) = function else {
                    panic!()
                };
                f.typed_parameters.groups[0].params[0].id = id;
            }
            _ => panic!(),
        }
        compiler.compile_run(&run, change).expect_err(
            "the exact two source clauses, positive domains and capture-free binders are required",
        );
    }
}
#[test]
fn multivariable_definition_rejects_future_limit_as_a_dimension_premise() {
    let (mut run, compiler) = super::execute(FIXED);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("the limit conclusion is invisible to all original prerequisite stages");
}
