use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const FROM: &str =
    include_str!("../../../lean/examples/second_partial_builtin_from_definition/statement.lit");
const TO: &str =
    include_str!("../../../lean/examples/second_partial_builtin_to_definition/statement.lit");
#[test]
fn second_partial_definition_schemas_keep_generic_coordinates_and_guarded_domains() {
    for source in [
        include_str!(
            "../../../lean/examples/second_partial_builtin_from_definition_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/second_partial_builtin_to_definition_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/second_partial_builtin_from_definition_guarded/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/second_partial_builtin_to_definition_guarded/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "second_definition_domain").unwrap();
    }
}
fn clause(run: &mut RunLitexCodeResult, fold: bool) -> &mut PlainExistFact {
    let b = invocation(run).builtin.as_mut().unwrap();
    let fact = if fold {
        &mut b.requirements[7]
    } else {
        &mut b.conclusions[0]
    };
    let Fact::ExistFact(e) = fact else {
        panic!("original local first-partial witness");
    };
    e
}
#[test]
fn second_partial_definition_schemas_replay_original_ordered_axes_and_local_witness() {
    for (source, id, law) in [
        (
            FROM,
            BuiltinTheoremId::SecondPartialAtFromDefinition,
            "secondPartialFromDefiningClause",
        ),
        (
            TO,
            BuiltinTheoremId::SecondPartialAtToDefinition,
            "secondPartialDefiningClause",
        ),
    ] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), 8);
        assert_eq!(p.dom_stores.len(), 8);
        assert_eq!(p.conclusions_wd.len(), 1);
        let output = c.compile_run(&run, "second_definition").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert!(output.contains("_multivariable_source_domain"));
        assert_eq!(output, c.compile_run(&run, "second_definition").unwrap());
    }
}
#[test]
fn second_partial_definition_schemas_require_every_original_stage() {
    for source in [FROM, TO] {
        for change in 0..8 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => {
                    p.dom_stores.pop();
                }
                2 => p.dom_proofs.swap(0, 3),
                3 => p.dom_stores.swap(0, 1),
                4 => p.conclusions_wd.clear(),
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p.builtin.as_mut().unwrap().arguments.clear(),
                _ => p.builtin.as_mut().unwrap().requirements.swap(5, 6),
            }
            assert!(
                c.compile_run(&run, "changed_second_definition_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_definition_schemas_keep_all_six_candidate_arguments() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..6 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let f = if fold {
                &mut b.conclusions[0]
            } else {
                &mut b.requirements[7]
            };
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = f else {
                panic!();
            };
            let mut arguments = p
                .relation
                .argument_refs()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            arguments[change] = super::number_object("9");
            p.relation = p.relation.with_arguments(&arguments);
            assert!(
                c.compile_run(&run, "changed_second_definition_argument")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_definition_schemas_preserve_local_set_function_and_binder_identity() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            let e = clause(&mut run, fold);
            match change {
                0 => {
                    e.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                1 => {
                    e.typed_parameters.groups[1].params[0].id =
                        e.typed_parameters.groups[0].params[0].id
                }
                2 => {
                    let ParamType::Obj(Obj::FunctionSpace(FunctionSpace::FnSet(s))) =
                        &mut e.typed_parameters.groups[1].param_type
                    else {
                        panic!();
                    };
                    s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
                }
                3 => {
                    e.facts.pop();
                }
                _ => e.facts.swap(0, 1),
            }
            assert!(
                c.compile_run(&run, "changed_second_definition_witness")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_definition_schemas_preserve_both_partial_subjects_and_ordered_axes() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let e = clause(&mut run, fold);
            let atom = if change < 2 {
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(q)) = &mut e.facts[2]
                else {
                    panic!();
                };
                let Obj::SetFormer(SetFormer::SetBuilder(b)) = &mut q.right else {
                    panic!();
                };
                let QuantifierFreeFact::AtomicFact(p) = &mut b.facts[0] else {
                    panic!();
                };
                p
            } else {
                let QuantifierFreeFact::AtomicFact(p) = &mut e.facts[3] else {
                    panic!();
                };
                p
            };
            let AtomicFact::MultivariableAnalysisFact(q) = atom else {
                panic!();
            };
            let MultivariableAnalysisRelation::PartialDerivativeAt(p) = &mut q.relation else {
                panic!();
            };
            if change % 2 == 0 {
                p.coordinate = super::number_object("9");
            } else {
                p.function = super::number_object("9");
            }
            assert!(
                c.compile_run(&run, "changed_local_partial_subject")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_definition_from_requires_original_complete_domain_and_real_value_formation() {
    for change in 0..4 {
        let (mut run, c) = super::execute(FROM);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut invocation(&mut run).conclusions_wd[0]
        else {
            panic!();
        };
        let PredicateDomainProof::MultivariableAnalysis(p) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!();
        };
        match change {
            0 => p.requirements.clear(),
            1 => p.function_domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            2 => {
                let Fact::AtomicFact(AtomicFact::InFact(q)) = &mut p.requirements[7].requirement
                else {
                    panic!();
                };
                q.set = Obj::StandardSet(StandardSet::C);
            }
            _ => p.requirements.swap(5, 6),
        }
        assert!(
            c.compile_run(&run, "changed_second_definition_formation")
                .is_err(),
            "{change}"
        );
    }
}
#[test]
fn second_partial_definition_to_requires_original_domain_inference_and_every_derived_store() {
    for change in 0..4 {
        let (mut run, c) = super::execute(TO);
        let p = invocation(&mut run);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &mut p.dom_stores[7].infer
        else {
            panic!();
        };
        let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0];
        match change {
            0 => capture.function_domain = None,
            1 => capture.derived.clear(),
            2 => capture.source_fact_id = capture.derived[0].primary_fact_id(),
            _ => capture.derived.swap(0, 1),
        }
        assert!(
            c.compile_run(&run, "changed_second_definition_inference")
                .is_err(),
            "{change}"
        );
    }
}
#[test]
fn second_partial_definition_to_cannot_cite_its_future_local_witness() {
    let (mut run, c) = super::execute(TO);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let checked = super::atomic_proof_mut(&mut p.dom_proofs[7]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
        &mut checked.searched_proof
    else {
        panic!("original source candidate citation");
    };
    cite.cite_fact_id = future;
    assert!(c
        .compile_run(&run, "future_second_partial_witness")
        .is_err());
}
