use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
const SELECTED: &str =
    include_str!("../../../lean/examples/multivariable_scalar_limit_selection/statement.lit");
#[test]
fn euclidean_scalar_selector_replays_candidates_existence_and_generic_dimensions() {
    for source in [
        SELECTED,
        include_str!("../../../lean/examples/multivariable_scalar_limit_existence/statement.lit"),
        include_str!(
            "../../../lean/examples/multivariable_scalar_limit_generic_dimension/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_scalar_limit_guarded_domain/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_scalar_limit_negative_citation/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_scalar_limit_nested_objects/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "scalar_euclidean_limit").expect(source);
    }
}
#[test]
fn euclidean_scalar_inference_requires_original_identity_domain_and_clause_order() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(SELECTED);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &mut p.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("multivariable inference");
        };
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition");
        };
        match mutation {
            0 => p.source_fact_id = FactId::new(u64::MAX),
            1 => p.function_domain = None,
            2 => p.derived.swap(0, 1),
            _ => {
                p.derived.pop();
            }
        }
        c.compile_run(&run, "changed_scalar_inference")
            .expect_err("source identity, optional route and exact clauses");
    }
}
#[test]
fn euclidean_scalar_predicate_formation_requires_dimension_and_point_contracts() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SELECTED);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut p.assumed_dom_facts[0].well_defined
        else {
            panic!("formation");
        };
        let PredicateDomainProof::MultivariableAnalysis(p) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("Euclidean formation");
        };
        match mutation {
            0 => {
                p.requirements.pop();
            }
            1 => p.requirements.swap(1, 2),
            _ => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0].requirement
                else {
                    panic!("positive dimension");
                };
                f.set = Obj::StandardSet(StandardSet::N);
            }
        }
        c.compile_run(&run, "changed_scalar_formation")
            .expect_err("ordered source carrier/dimension requirements");
    }
}
#[test]
fn euclidean_scalar_selector_rejects_missing_original_wd_children() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, LimitOperatorObjWellDefinedProofByDef,
        ObjWellDefinedProofByDef,
    };
    let (mut run, c) = super::execute(SELECTED);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(
                LimitOperatorObjWellDefinedProofByDef::MultivariableScalar(p),
            ),
        ..
    } = p
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("scalar selector WD");
    };
    p.stages.argument_well_defined.pop();
    c.compile_run(&run, "missing_scalar_child")
        .expect_err("all original constructor arguments");
}

#[test]
fn function_alpha_renaming_preserves_free_coordinate_references() {
    use crate::compile_to_lean::helper::instantiated_object_matches;
    use std::collections::{HashMap, HashSet};
    let (mut run, mut compiler) = super::execute(include_str!(
        "../../../lean/examples/multivariable_scalar_limit_from_definition/statement.lit"
    ));
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let Fact::ForallFact(acc) = &root.fact.dom_facts[0] else {
        panic!("accumulation premise");
    };
    let [ExistOrAndChainAtomicFact::ExistFact(witness)] = acc.then_facts.as_slice() else {
        panic!("witness");
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(lower)) = &witness.facts[0] else {
        panic!("puncture");
    };
    let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) = &lower.right else {
        panic!("Euclidean distance");
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = norm.vector.as_ref() else {
        panic!("coordinate difference");
    };
    let original = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(&original, &HashSet::new(), &mut free);
    let capture = *free.iter().next().unwrap();
    for (id, expected) in [(IdentifierId::new(u64::MAX), true), (capture, false)] {
        let mut renamed = function.clone();
        let old = renamed.body.set_bound_parameters.groups[0].params[0].clone();
        let mut new = old.clone();
        new.id = id;
        renamed.body.set_bound_parameters.groups[0].params[0] = new.clone();
        renamed.equal_to = Box::new(
            compiler
                .runtime
                .inst_obj(
                    &function.equal_to,
                    &HashMap::from([(
                        old.id,
                        Obj::Identifier(IdentifierObj::from_bound_name(&new)),
                    )]),
                )
                .unwrap(),
        );
        assert_eq!(
            instantiated_object_matches(
                &original,
                &Obj::FunctionSpace(FunctionSpace::AnonymousFn(renamed)),
                &HashMap::new()
            ),
            expected
        );
    }
}

#[test]
fn euclidean_scalar_definition_replays_its_original_clauses() {
    let (run, c) = super::execute(include_str!(
        "../../../lean/examples/multivariable_scalar_limit_from_definition/statement.lit"
    ));
    let lean = c.compile_run(&run, "scalar_euclidean_definition").unwrap();
    assert!(lean.contains("_multivariable_clause_0"));
    assert!(lean.contains("_multivariable_clause_1"));
}
