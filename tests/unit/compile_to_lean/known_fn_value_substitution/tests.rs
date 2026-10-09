use crate::prelude::*;

const SOURCE: &str = "have fn shift(x R) R=x+3\nhave x R\nshift(x)=x+3\n2*shift(x)=2*x+6\n";

fn rewrite(statement: &mut ExecStmtResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::known_fn_value_substitution_builtin_rewrite_proof::KnownFnValueSubstitutionBuiltinRewriteProof{
    let proof = super::equality_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let EqualFactSearchedProof::ByBuiltinRewrite(
        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::KnownFnValueSubstitution(proof),
    )=&mut proof.searched_proof else {panic!("actual new rewrite route")};
    proof
}

#[test]
fn known_fn_value_substitution_replays_the_actual_call_equation_and_child() {
    let (mut result, compiler) = super::execute(SOURCE);
    let id =
        super::equality_proof(&super::fact_statement(&result.statement_results[2]).verify_result)
            .fact
            .fact_id;
    assert_eq!(
        rewrite(&mut result.statement_results[3]).cited_equal_fact_ids,
        vec![id]
    );
    let output = super::compile_run(&result, &compiler, "known_fn_value_affine")
        .expect("cited function-value replay");
    assert!(output.contains(&format!("h_{}", id.value())));
    assert!(output.contains("congrArg₂ M.mulValue"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn known_fn_value_substitution_rejects_deleted_duplicate_wrong_and_unused_citations() {
    let source = "have fn shift(x R) R=x+3\nhave x R\nx=x\nshift(x)=x+3\n2*shift(x)=2*x+6\n";
    for change in ["deleted", "duplicate", "wrong", "unused"] {
        let (mut result, compiler) = super::execute(source);
        let unrelated = super::equality_proof(
            &super::fact_statement(&result.statement_results[2]).verify_result,
        )
        .fact
        .fact_id;
        let ids = &mut rewrite(&mut result.statement_results[4]).cited_equal_fact_ids;
        match change {
            "deleted" => ids.clear(),
            "duplicate" => ids.push(ids[0]),
            "wrong" => ids[0] = unrelated,
            "unused" => ids.push(unrelated),
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["EqualityRewrite/", "FactId/"]);
    }
}

#[test]
fn known_fn_value_substitution_rejects_changed_endpoints_or_unrelated_residual() {
    let (mut result, compiler) = super::execute(SOURCE);
    rewrite(&mut result.statement_results[3]).rewritten_left = super::number_object("2");
    super::phase2_rejected(
        &result,
        &compiler,
        "changed_fn_value_residual",
        &["EqualityRewrite/Residual"],
    );

    let source = "have fn shift(x R) R=x+3\nhave x R\nx=x\nshift(x)=x+3\n2*shift(x)=2*x+6\n";
    let (mut result, compiler) = super::execute(source);
    let unrelated = match result.statement_results.remove(2) {
        ExecStmtResult::Fact(crate::execute::ExecFactStmtResult::Success(proof)) => {
            proof.verify_result
        }
        _ => panic!("actual unrelated verification"),
    };
    rewrite(&mut result.statement_results[3]).residual_equal = unrelated;
    super::phase2_rejected(
        &result,
        &compiler,
        "unrelated_fn_value_residual",
        &["EqualityRewrite/Residual"],
    );
}

#[test]
fn known_fn_value_substitution_preserves_both_side_citation_order() {
    let source="have fn left(x R) R=x+1\nhave fn right(x R) R=x-1\nhave x R\nleft(x)=x+1\nright(x)=x-1\nleft(x)+left(x)=2*right(x)+4\n";
    let (mut result, compiler) = super::execute(source);
    super::compile_run(&result, &compiler, "fn_value_both_sides").expect("both-side replay");
    let ids = &mut rewrite(&mut result.statement_results[5]).cited_equal_fact_ids;
    assert_eq!(ids.len(), 2);
    ids.swap(0, 1);
    super::phase2_rejected(
        &result,
        &compiler,
        "reordered_fn_values",
        &["EqualityRewrite/CitationOrder"],
    );
}

#[test]
fn known_fn_value_substitution_cannot_cite_an_equality_from_a_closed_scope() {
    let source="have fn shift(x R) R=x+3\nforall x R:\n    shift(x)=x+3\n    =>:\n        x=x\nhave x R\nshift(x)=x+3\n2*shift(x)=2*x+6\n";
    let (mut result, compiler) = super::execute(source);
    super::compile_run(&result, &compiler, "fn_value_scope_before_tampering")
        .expect("actual visible source compiles");
    let local = super::forall_proof(&result.statement_results[1]).assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    rewrite(&mut result.statement_results[4]).cited_equal_fact_ids[0] = local;
    super::phase2_rejected(
        &result,
        &compiler,
        "closed_fn_value_origin",
        &["FactId/Resolution"],
    );
}
