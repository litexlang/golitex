use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::FunctionBodySourceProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::fn_application_unfold_substitution_builtin_rewrite_proof::FnApplicationUnfoldSubstitutionBuiltinRewriteProof;

const SOURCE: &str = "have fn shift(t R) R=t+3\nhave x R\n2*shift(x)=2*x+6\n";

fn rewrite(
    statement: &mut ExecStmtResult,
) -> &mut FnApplicationUnfoldSubstitutionBuiltinRewriteProof {
    let proof = super::equality_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let EqualFactSearchedProof::ByBuiltinRewrite(
        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(proof),
    ) = &mut proof.searched_proof else { panic!("actual definition rewrite") };
    proof
}

#[test]
fn fn_application_unfold_substitution_replays_head_equality_beta_and_residual() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = rewrite(&mut result.statement_results[2]);
    let FunctionBodySourceProof::KnownEquality(path) = &proof.expansions[0].function_body else {
        panic!("source")
    };
    let id = path.path[0].2;
    let output =
        super::compile_run(&result, &compiler, "definition_affine").expect("exact beta replay");
    assert!(output.contains(&format!("h_{}", id.value())));
    assert!(output.contains("Litex.callFormula_denote") && output.contains("congrArg₂ M.mulValue"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn fn_application_unfold_substitution_rejects_missing_or_reordered_steps() {
    let source = "have fn f(t R) R=t+1\nhave fn g(t R) R=t-1\nhave x R\nf(x)+f(x)=2*g(x)+4\n";
    for change in ["deleted", "missing", "reordered"] {
        let (mut result, compiler) = super::execute(source);
        super::compile_run(&result, &compiler, "original_order").unwrap();
        let steps = &mut rewrite(&mut result.statement_results[3]).expansions;
        match change {
            "deleted" => steps.clear(),
            "missing" => {
                steps.pop();
            }
            "reordered" => steps.swap(0, 2),
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["EqualityRewrite/", "WD/"]);
    }
}

#[test]
fn fn_application_unfold_substitution_rejects_changed_body_and_application() {
    for change in ["body", "application", "continued"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let step = &mut rewrite(&mut result.statement_results[2]).expansions[0];
        match change {
            "body" => step.expanded_body = super::number_object("7"),
            "application" => step.application = super::number_object("7"),
            "continued" => step.continued_body = super::number_object("7"),
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["EqualityRewrite/", "FunctionDefinition/"],
        );
    }
}

#[test]
fn fn_application_unfold_substitution_rejects_wrong_definition_citation() {
    let source = "have fn f(t R) R=t+1\nhave fn g(t R) R=t+2\nhave x R\nx=x\n2*f(x)=2*x+2";
    let (mut result, compiler) = super::execute(source);
    let wrong =
        super::equality_proof(&super::fact_statement(&result.statement_results[3]).verify_result)
            .fact
            .fact_id;
    let FunctionBodySourceProof::KnownEquality(path) =
        &mut rewrite(&mut result.statement_results[4]).expansions[0].function_body
    else {
        panic!("source")
    };
    path.path[0].2 = wrong;
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_head_source",
        &["Equality/Path", "FactId/"],
    );
}

#[test]
fn fn_application_unfold_substitution_rejects_deleted_source_path() {
    let (mut result, compiler) = super::execute(SOURCE);
    let FunctionBodySourceProof::KnownEquality(path) =
        &mut rewrite(&mut result.statement_results[2]).expansions[0].function_body
    else {
        panic!("source")
    };
    path.path.clear();
    super::phase2_rejected(
        &result,
        &compiler,
        "missing_head_source",
        &["EqualityRewrite/Expansion"],
    );
}

#[test]
fn fn_application_unfold_substitution_rejects_changed_endpoints_and_unrelated_residual() {
    let (mut result, compiler) = super::execute(SOURCE);
    rewrite(&mut result.statement_results[2]).rewritten_left = super::number_object("2");
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_residual_endpoint",
        &["EqualityRewrite/Residual"],
    );
    let (mut result, compiler) =
        super::execute("have fn shift(t R) R=t+3\nhave x R\nx=x\n2*shift(x)=2*x+6");
    let unrelated = match result.statement_results.remove(2) {
        ExecStmtResult::Fact(crate::execute::ExecFactStmtResult::Success(p)) => p.verify_result,
        _ => panic!("equality"),
    };
    rewrite(&mut result.statement_results[2]).residual_equal = unrelated;
    super::phase2_rejected(
        &result,
        &compiler,
        "unrelated_residual",
        &["EqualityRewrite/Residual"],
    );
}

#[test]
fn fn_application_unfold_substitution_rejects_a_closed_scope_citation() {
    let source =
        "have fn f(t R) R=t+1\nforall x R:\n    x=x\n    =>:\n        x=x\nhave y R\n2*f(y)=2*y+2";
    let (mut result, compiler) = super::execute(source);
    super::compile_run(&result, &compiler, "visible_definition").unwrap();
    let local = super::forall_proof(&result.statement_results[1]).assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    let FunctionBodySourceProof::KnownEquality(path) =
        &mut rewrite(&mut result.statement_results[3]).expansions[0].function_body
    else {
        panic!("source")
    };
    path.path[0].2 = local;
    super::phase2_rejected(
        &result,
        &compiler,
        "closed_definition_citation",
        &["FactId/Resolution"],
    );
}

#[test]
fn fn_application_unfold_substitution_examples_replay_without_holes() {
    for suffix in [
        "_multiple_calls",
        "_exact_arguments",
        "_duplicate_sources",
        "_guarded",
    ] {
        let path=std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution{suffix}.lit"));
        let (result, compiler) = super::execute(&std::fs::read_to_string(path).unwrap());
        let output = super::compile_run(&result, &compiler, "definition_examples")
            .unwrap_or_else(|e| panic!("{suffix}: {}", e.route));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn fn_application_unfold_substitution_keeps_unsupported_residual_fail_closed() {
    let source=include_str!("../../../../examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution_scalar_arithmetic.lit");
    let (result, compiler) = super::execute(source);
    let error = super::compile_run(&result, &compiler, "unsupported_residual")
        .expect_err("unsupported successful child rejects the whole artifact");
    assert_eq!(error.route, "Equality/BuiltinStrategy");
}

#[test]
fn fn_application_unfold_substitution_preserves_existing_natural_definition_compiler_boundary() {
    let source=include_str!("../../../../examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution.lit");
    let (result, compiler) = super::execute(source);
    let error = super::compile_run(&result, &compiler, "natural_definition_unsupported")
        .expect_err("existing natural function declaration producer remains unsupported");
    assert_eq!(error.route, "WD/Producer");
}
