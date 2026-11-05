use crate::prelude::*;

#[test]
fn vector_limit_formation_preserves_independent_output_dimension_and_stage_order() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    let source = r#"# Select a three-dimensional vector limit from a two-dimensional input and cite its value.
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), L cart_n(R,3):
    $has_vector_limit_at(f,p,2,3,L)
    =>:
        lim_vector_at(f,p,2,3)=L
        lim_vector_at(f,p,2,3) $in cart_n(R,3)
"#;
    for mutation in 0..3 {
        let (mut run, c) = super::execute(source);
        let proof = super::forall_proof_mut(&mut run.statement_results[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut proof.assumed_dom_facts[0].well_defined
        else {
            panic!("formation")
        };
        let PredicateDomainProof::MultivariableAnalysis(p) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("vector formation")
        };
        match mutation {
            0 => {
                p.requirements.swap(0, 2);
            }
            1 => {
                p.requirements.pop();
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2].requirement
                else {
                    panic!("output dimension")
                };
                f.set = Obj::StandardSet(StandardSet::N);
            }
        }
        c.compile_run(&run, "changed_vector_formation")
            .expect_err("source dimension and ordered requirements");
    }
}
#[test]
fn vector_limit_inferences_retain_source_identity_domain_and_clause_order() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    let source = r#"# Select a three-dimensional vector limit from a two-dimensional input and cite its value.
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), L cart_n(R,3):
    $has_vector_limit_at(f,p,2,3,L)
    =>:
        lim_vector_at(f,p,2,3)=L
        lim_vector_at(f,p,2,3) $in cart_n(R,3)
"#;
    for mutation in 0..3 {
        let (mut run, c) = super::execute(source);
        let proof = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &mut proof.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("inference")
        };
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition")
        };
        match mutation {
            0 => p.source_fact_id = FactId::new(u64::MAX),
            1 => p.function_domain = None,
            _ => p.derived.swap(0, 1),
        }
        c.compile_run(&run, "changed_vector_inference")
            .expect_err("exact producer and clauses");
    }
}
#[test]
fn vector_limit_requires_original_output_wd_child() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, LimitOperatorObjWellDefinedProofByDef,
        ObjWellDefinedProofByDef,
    };
    let (mut run, c) = super::execute(
        r#"# Select a three-dimensional vector limit from a two-dimensional input and cite its value.
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), L cart_n(R,3):
    $has_vector_limit_at(f,p,2,3,L)
    =>:
        lim_vector_at(f,p,2,3)=L
        lim_vector_at(f,p,2,3) $in cart_n(R,3)
"#,
    );
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(
                LimitOperatorObjWellDefinedProofByDef::MultivariableVector(p),
            ),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("vector WD")
    };
    p.stages.argument_well_defined.pop();
    c.compile_run(&run, "missing_vector_output_dimension")
        .expect_err("four original children");
}
