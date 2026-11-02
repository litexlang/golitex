use crate::prelude::*;

#[test]
fn curl_replays_selection_existence_and_six_partial_definition() {
    for source in [
        include_str!("../../../lean/examples/curl_selection/statement.lit"),
        include_str!("../../../lean/examples/curl_existence/statement.lit"),
        include_str!("../../../lean/examples/curl_guarded_domain/statement.lit"),
        include_str!("../../../lean/examples/curl_from_partials/statement.lit"),
        include_str!("../../../lean/examples/curl_negative_citation/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "curl_replay").expect(source);
    }
}

#[test]
fn curl_rejects_changed_domains_and_inference_producers() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for mutation in 0..4 {
        let (mut run, c) = super::execute(include_str!(
            "../../../lean/examples/curl_selection/statement.lit"
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
                panic!("curl")
            };
            let i = if mutation == 0 { 5 } else { 6 };
            let Fact::AtomicFact(AtomicFact::InFact(q)) = &mut p.requirements[i].requirement else {
                panic!("domain")
            };
            q.set = Obj::StandardSet(StandardSet::C);
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
        c.compile_run(&run, "altered_curl")
            .expect_err("preserve original subjects and evidence");
    }
}

#[test]
fn curl_requires_original_point_wd() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, ObjWellDefinedProofByDef,
    };
    let (mut run, c) = super::execute(include_str!(
        "../../../lean/examples/curl_selection/statement.lit"
    ));
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::DerivativeOperator(DerivativeOperatorWellDefinedProof::Curl(p)),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("curl selector")
    };
    p.stages.argument_well_defined.pop();
    c.compile_run(&run, "missing_curl_point")
        .expect_err("original point WD required");
}
