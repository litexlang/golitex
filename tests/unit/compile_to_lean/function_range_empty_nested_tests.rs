use crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof;
use crate::prelude::*;

const SOURCE: &str = "forall source_x R:\n    source_x=source_x\nforall B set,f fn(target_y R:target_y!=target_y) B:\n    fn_range(f)={}\n";

const BINARY: &str = "forall source_u,source_v R:\n    source_u=source_u\nforall B set,f fn(target_x,target_y R:target_x!=target_x) B:\n    fn_range(f)={}\n";
const RETURNED: &str = "forall source_u R:\n    source_u=source_u\nforall B set,h fn(t R) fn(y R:y!=y) B,a R:\n    fn_range(h(a))={}\n";
const SIBLING: &str = "forall source_x R:\n    source_x=source_x\nforall private_f fn(private_x R:private_x!=private_x) R:\n    fn_range(private_f)={}\nforall B set,f fn(target_y R:target_y!=target_y) B:\n    fn_range(f)={}\n";

const STORED_SIBLING: &str = "forall source_x R:\n    source_x=source_x\nforall private_tag R:\n    forall private_x R:\n        private_x=private_x\n    =>:\n        private_tag=private_tag\nforall B set,f fn(target_y R:target_y!=target_y) B:\n    fn_range(f)={}\n";

fn last_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    super::equality_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result)
}
fn nested_reuse(equality: &mut VerifyEqualitySuccess) -> &mut VerifyKnownForallFactProof {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::FnRangeOfEmptyDomain(p),
    ) = &mut equality.searched_proof
    else {
        panic!("original empty-range rule")
    };
    let FunctionDomainEmptyProof::GuardExclusion(p) = &mut p.domain_empty else {
        panic!("original guard exclusion")
    };
    let VerifyFactResult::ForallFact(p) = p.exclusion.as_mut() else {
        panic!("original forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) = p.as_mut()
    else {
        panic!("original whole-forall child")
    };
    p
}
fn reuse(run: &mut RunLitexCodeResult) -> &mut VerifyKnownForallFactProof {
    nested_reuse(last_equality(run))
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    assert!(super::compile_run(run, compiler, "changed_nested_empty_range").is_err());
}

#[test]
fn range_empty_nested_whole_forall_replays_original_citation_and_renaming() {
    for source in [SOURCE, BINARY, RETURNED, SIBLING, STORED_SIBLING] {
        let (mut run, compiler) = super::execute(source);
        let first = super::forall_proof_mut(&mut run.statement_results[0])
            .fact
            .fact_id;
        let p = reuse(&mut run);
        assert_eq!(p.cite_fact_id, first);
        assert_eq!(
            p.parameter_renamings.len(),
            if source == BINARY { 2 } else { 1 }
        );
        assert!(p.parameter_renamings.iter().all(|r| r.source != r.target));
        let output = super::compile_run(&run, &compiler, "nested_empty_range").unwrap();
        assert!(output.contains("Litex.fnRangeEmptyOfDomainEmpty"));
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "nested_empty_range").unwrap()
        );
    }
}

#[test]
fn range_empty_nested_whole_forall_rejects_missing_and_future_citations() {
    for future in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let future_id = last_equality(&mut run).fact.fact_id;
        reuse(&mut run).cite_fact_id = if future {
            future_id
        } else {
            FactId::new(9_030_001)
        };
        reject(&run, &compiler);
    }
}

#[test]
fn range_empty_nested_whole_forall_requires_exact_ordered_binder_renaming() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = reuse(&mut run);
        match mutation {
            0 => p.parameter_renamings.clear(),
            1 => p.parameter_renamings[0].source = IdentifierId::new(9_030_002),
            _ => p.parameter_renamings[0].target = IdentifierId::new(9_030_003),
        }
        reject(&run, &compiler);
    }
}

#[test]
fn range_empty_nested_whole_forall_keeps_original_conclusion_formation() {
    let (mut run, compiler) = super::execute(SOURCE);
    let p = reuse(&mut run);
    assert_eq!(p.well_defined.detailed_ref().then.len(), 1);
    p.well_defined.as_detailed_mut().unwrap().then.clear();
    reject(&run, &compiler);
}

#[test]
fn range_empty_nested_whole_forall_keeps_original_parameter_formation() {
    let (mut run, compiler) = super::execute(SOURCE);
    reuse(&mut run)
        .well_defined
        .as_detailed_mut()
        .unwrap()
        .introduced_params
        .param_type_well_defined
        .clear();
    reject(&run, &compiler);
}

#[test]
fn range_empty_nested_whole_forall_cannot_cite_an_unpublished_sibling_child() {
    let (mut run, compiler) = super::execute(SIBLING);
    super::compile_run(&run, &compiler, "nested_original_sibling").unwrap();
    let sibling = super::forall_proof_mut(&mut run.statement_results[1]);
    let equality =
        super::equality_proof_mut(&mut sibling.proved_then_facts.last_mut().unwrap().verify_result);
    let sibling_id = nested_reuse(equality).fact.fact_id;
    assert_ne!(reuse(&mut run).cite_fact_id, sibling_id);
    reuse(&mut run).cite_fact_id = sibling_id;
    reject(&run, &compiler);
}

#[test]
fn range_empty_nested_whole_forall_rejects_swapped_and_duplicated_two_binder_maps() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(BINARY);
        let p = reuse(&mut run);
        assert_eq!(p.parameter_renamings.len(), 2);
        match mutation {
            0 => p.parameter_renamings.swap(0, 1),
            1 => p.parameter_renamings[1].source = p.parameter_renamings[0].source,
            _ => p.parameter_renamings[1].target = p.parameter_renamings[0].target,
        }
        reject(&run, &compiler);
    }
}

#[test]
fn range_empty_nested_whole_forall_rejects_a_matching_stored_closed_sibling() {
    let (mut run, compiler) = super::execute(STORED_SIBLING);
    super::compile_run(&run, &compiler, "original_stored_sibling").unwrap();
    let sibling = super::forall_proof_mut(&mut run.statement_results[1]);
    let StoreFactResult::ForallFact(store) = &sibling.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!("actual private stored universal premise")
    };
    assert_eq!(store.fact_id, sibling.fact.dom_facts[0].fact_id());
    let foreign_id = store.fact_id;
    let foreign_binder = store.fact.typed_parameters.groups[0].params[0].id;
    let p = reuse(&mut run);
    assert_ne!(p.cite_fact_id, foreign_id);
    assert_eq!(p.parameter_renamings.len(), 1);
    p.cite_fact_id = foreign_id;
    p.parameter_renamings[0].source = foreign_binder;
    let error = super::compile_run(&run, &compiler, "closed_stored_sibling").unwrap_err();
    assert!(
        matches!(
            error.route.as_str(),
            "FactId/Resolution" | "FactId/Producer"
        ),
        "{error:?}"
    );
}
