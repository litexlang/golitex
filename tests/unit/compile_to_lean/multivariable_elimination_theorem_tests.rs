use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const DEFINITION: &str = include_str!(
    "../../../lean/examples/multivariable_limit_builtin_epsilon_control/statement.lit"
);
const EXISTS: &str =
    include_str!("../../../lean/examples/multivariable_limit_builtin_exists/statement.lit");
const UNIQUE: &str =
    include_str!("../../../lean/examples/multivariable_limit_builtin_unique/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/multivariable_limit_builtin_selected/statement.lit");

#[test]
fn multivariable_elimination_replays_original_candidates_and_captured_domain() {
    for (source, law) in [
        (DEFINITION, "Litex.multivariableScalarLimitClauses"),
        (EXISTS, "Litex.multivariableScalarExistsOfCandidate"),
        (UNIQUE, "Litex.multivariableScalarLimitUnique"),
        (SELECTED, "Litex.multivariableScalarLimitValueSelected"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "multi_elimination").unwrap();
        assert!(output.contains(law));
        assert_eq!(
            output,
            compiler.compile_run(&run, "multi_elimination").unwrap()
        );
    }
}

#[test]
fn multivariable_elimination_selected_retains_original_existence_domain_and_selector() {
    for change in ["existence", "selector", "domain", "nested_wd"] {
        let (mut run, compiler) = super::execute(SELECTED);
        let p = invocation(&mut run);
        match change {
            "existence" => {
                let Fact::ExistFact(e) = &mut p.builtin.as_mut().unwrap().requirements[4] else {
                    panic!()
                };
                e.facts.clear();
            }
            "selector" => {
                let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                let MultivariableAnalysisRelation::ScalarLimit(r) = &mut f.relation else {
                    panic!()
                };
                let Obj::LimitOperator(LimitOperator::MultivariableScalar(s)) = &mut r.value else {
                    panic!()
                };
                s.dimension = Box::new(super::number_object("3"));
            }
            _ => {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                let wd = wd.as_detailed_mut().unwrap();
                if change == "nested_wd" {
                    wd.well_defined_of_each_parameter.clear();
                } else {
                    let crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof::MultivariableAnalysis(capture) = &mut wd.predicate_domain else { panic!() };
                    capture.function_domain.signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::C));
                }
            }
        }
        compiler.compile_run(&run, change).expect_err("selection retains the original real existence premise, complete domain and exact selector WD");
    }
}

#[test]
fn multivariable_elimination_preserves_each_original_stage_and_both_output_formations() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "store_order",
        "types",
        "wd",
        "second_wd",
    ] {
        let (mut run, compiler) = super::execute(DEFINITION);
        let p = invocation(&mut run);
        match change {
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(0, 4),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 4),
            "types" => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
            "wd" => p.conclusions_wd.clear(),
            _ => {
                p.conclusions_wd.pop();
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("no original stage or output formation may be omitted or reordered");
    }
}

#[test]
fn multivariable_elimination_requires_original_inference_identity_and_complete_domain() {
    for change in ["missing", "identity", "derived", "domain", "signature"] {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        if change == "missing" {
            p.dom_stores[4].infer = None;
        } else {
            let other_id = p.builtin.as_ref().unwrap().requirements[5].fact_id();
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[4].infer
            else {
                panic!()
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice()
            else {
                panic!()
            };
            match change {
                "identity" => capture.source_fact_id = other_id,
                "derived" => capture.derived.clear(),
                "domain" => capture.function_domain = None,
                _ => {
                    capture.function_domain.as_mut().unwrap().signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::C))
                }
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "only the candidate's recorded complete-domain inference can certify this elimination",
        );
    }
}

#[test]
fn multivariable_elimination_retains_both_exact_definition_clauses() {
    for change in ["accumulation", "epsilon", "positive_radius", "guard"] {
        let (mut run, compiler) = super::execute(DEFINITION);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = p.requirements[0].clone();
        let index = usize::from(change == "epsilon");
        let Fact::ForallFact(f) = &mut p.conclusions[index] else {
            panic!()
        };
        match change {
            "accumulation" | "epsilon" => f.then_facts.clear(),
            "positive_radius" => {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            _ => f.dom_facts.push(guard),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("both original positive-radius and epsilon clauses are required");
    }
}

#[test]
fn multivariable_elimination_rejects_future_conclusion_as_an_original_premise() {
    let (mut run, compiler) = super::execute(UNIQUE);
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
        .expect_err("an elimination conclusion is invisible to its prerequisites");
}
