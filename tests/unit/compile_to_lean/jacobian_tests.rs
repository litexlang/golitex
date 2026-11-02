use crate::prelude::*;

#[test]
fn jacobians_replay_rectangular_selection_existence_and_definition() {
    for source in [
        include_str!("../../../lean/examples/jacobian_selection/statement.lit"),
        include_str!("../../../lean/examples/jacobian_generic_dimensions/statement.lit"),
        include_str!("../../../lean/examples/jacobian_existence/statement.lit"),
        include_str!("../../../lean/examples/jacobian_guarded_domain/statement.lit"),
        include_str!("../../../lean/examples/jacobian_negative_citation/statement.lit"),
        include_str!("../../../lean/examples/jacobian_from_partials/statement.lit"),
        include_str!("../../../lean/examples/jacobian_nested_objects/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "jacobian_replay").expect(source);
    }
}

#[test]
fn jacobians_reject_changed_domains_dimensions_and_inference_subjects() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for mutation in 0..4 {
        let (mut run, c) = super::execute(include_str!(
            "../../../lean/examples/jacobian_selection/statement.lit"
        ));
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        if mutation < 2 {
            let FactWellDefinedProof::AtomicExceptEquality(p) =
                &mut root.assumed_dom_facts[0].well_defined
            else {
                panic!("atomic")
            };
            let PredicateDomainProof::MultivariableAnalysis(p) =
                &mut p.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("jacobian")
            };
            if mutation == 0 {
                let Fact::AtomicFact(AtomicFact::InFact(q)) = &mut p.requirements[5].requirement
                else {
                    panic!("domain")
                };
                q.set = Obj::StandardSet(StandardSet::R);
            } else {
                let Fact::AtomicFact(AtomicFact::InFact(q)) = &mut p.requirements[6].requirement
                else {
                    panic!("matrix")
                };
                let Obj::SetFormer(SetFormer::MatrixSet(matrix)) = &mut q.set else {
                    panic!("carrier")
                };
                std::mem::swap(&mut matrix.rows, &mut matrix.cols);
            }
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
            if mutation == 2 {
                p.source_fact_id = FactId::new(u64::MAX);
            } else {
                p.derived.swap(0, 1);
            }
        }
        c.compile_run(&run, "altered_jacobian")
            .expect_err("retain original subjects and dimensions");
    }
}

#[test]
fn jacobians_require_all_original_constructor_arguments() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, ObjWellDefinedProofByDef,
    };
    let (mut run, c) = super::execute(include_str!(
        "../../../lean/examples/jacobian_selection/statement.lit"
    ));
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::DerivativeOperator(DerivativeOperatorWellDefinedProof::Jacobian(
                p,
            )),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("jacobian selector")
    };
    p.stages.argument_well_defined.pop();
    c.compile_run(&run, "missing_jacobian_dimension")
        .expect_err("original output dimension WD is required");
}
