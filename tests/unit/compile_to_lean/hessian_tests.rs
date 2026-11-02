use crate::prelude::*;
#[test]
fn hessians_replay_selection_existence_coordinates_and_partial_definition() {
    for source in [
        include_str!("../../../lean/examples/hessian_selection/statement.lit"),
        include_str!("../../../lean/examples/hessian_existence/statement.lit"),
        include_str!("../../../lean/examples/hessian_generic_dimension/statement.lit"),
        include_str!("../../../lean/examples/hessian_negative_citation/statement.lit"),
        include_str!("../../../lean/examples/hessian_from_second_partials/statement.lit"),
        include_str!("../../../lean/examples/hessian_guarded_domain/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "hessian_replay").expect(source);
    }
}
#[test]
fn hessians_reject_changed_point_domain_and_inference_subjects() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for mutation in 0..3 {
        let (mut run, c) = super::execute(include_str!(
            "../../../lean/examples/hessian_selection/statement.lit"
        ));
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        if mutation == 0 {
            let FactWellDefinedProof::AtomicExceptEquality(p) =
                &mut root.assumed_dom_facts[0].well_defined
            else {
                panic!("atomic")
            };
            let PredicateDomainProof::MultivariableAnalysis(p) =
                &mut p.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("hessian")
            };
            let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut p.requirements[4].requirement
            else {
                panic!("point domain")
            };
            member.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut root.assumed_dom_facts[0].store_and_infer.infer
            else {
                panic!("inference")
            };
            let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice() else {
                panic!("definition")
            };
            if mutation == 1 {
                p.source_fact_id = FactId::new(u64::MAX)
            } else {
                p.derived.swap(0, 1)
            }
        }
        c.compile_run(&run, "changed_hessian_evidence")
            .expect_err("original point/domain/definition evidence");
    }
}
