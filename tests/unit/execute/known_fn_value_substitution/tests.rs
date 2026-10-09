use crate::prelude::*;

const AFFINE: &str =
    "have fn shift(x R) R = x + 3\nhave x R\nshift(x) = x + 3\n2 * shift(x) = 2 * x + 6\n";

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn verified(runtime: &mut Runtime, source: &str) -> RunLitexCodeResult {
    let result = runtime.run_litex_code(source).expect("source execution");
    assert!(result.success && result.session_error.is_none(), "{source}");
    result
}

fn rejected(runtime: &mut Runtime, source: &str) -> RunLitexCodeResult {
    let result = runtime.run_litex_code(source).expect("soft source failure");
    assert!(
        !result.success && result.session_error.is_none(),
        "{source}"
    );
    assert_eq!(runtime.execution_environments_stack.len(), 1);
    result
}

fn equality(statement: &ExecStmtResult) -> &VerifyEqualitySuccess {
    let ExecStmtResult::Fact(crate::execute::ExecFactStmtResult::Success(statement)) = statement
    else {
        panic!("successful fact statement");
    };
    let VerifyFactResult::Equality(result) = &statement.verify_result else {
        panic!("equality verification");
    };
    let VerifyEqualityResult::Success(proof) = result.as_ref() else {
        panic!("successful equality");
    };
    proof
}

#[test]
fn affine_endpoint_retains_exact_citation_and_residual_evidence() {
    let mut runtime = runtime();
    let result = verified(&mut runtime, AFFINE);
    let source = equality(&result.statement_results[2]);
    let target = equality(&result.statement_results[3]);
    let EqualFactSearchedProof::ByBuiltinRewrite(
        super::super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::KnownFnValueSubstitution(proof),
    ) = &target.searched_proof else {
        panic!("the new function-value rewrite must win");
    };
    assert_eq!(proof.cited_equal_fact_ids, vec![source.fact.fact_id]);
    let VerifyFactResult::Equality(residual) = &proof.residual_equal else {
        panic!("equality residual");
    };
    let VerifyEqualityResult::Success(residual) = residual.as_ref() else {
        panic!("successful residual");
    };
    assert_eq!(residual.fact.left.ir(), proof.rewritten_left.ir());
    assert_eq!(residual.fact.right.ir(), proof.rewritten_right.ir());
    assert!(matches!(
        residual.searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(_)
    ));
    let detail = crate::json_output::project_stmt_detailed(&result.statement_results[3], &runtime)
        .stringify();
    assert!(detail.contains("KnownFnValueSubstitution"));
    assert!(detail.contains(&source.fact.fact_id.to_string()));
    assert!(detail.contains("residual_equal"));
    crate::json_output::project_stmt_normal(&result.statement_results[3], &runtime);
}

#[test]
fn actual_textbook_and_showcase_coordinates_use_the_short_endpoints() {
    let mut runtime = runtime();
    let source = include_str!(
        "../../../../examples/proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution.lit"
    );
    verified(&mut runtime, source);
    let result = verified(
        &mut runtime,
        "forall x,y R:\n    (x,y)(1)=x\n    (-x,-y)(1)=-x\n    (x,y)(1)+(-x,-y)(1)=0\n",
    );
    assert!(
        crate::json_output::project_run_detailed(&result, &runtime, "eval", None)
            .stringify()
            .contains("KnownFnValueSubstitution")
    );
}

#[test]
fn both_sides_multiple_values_and_repeated_calls_share_one_pass() {
    let mut runtime = runtime();
    let result = verified(&mut runtime, "have fn left(x R) R = x + 1\nhave fn right(x R) R = x - 1\nhave x R\nleft(x)=x+1\nright(x)=x-1\nleft(x)+left(x)=2*right(x)+4\n");
    let target = equality(&result.statement_results[5]);
    let EqualFactSearchedProof::ByBuiltinRewrite(
        super::super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::KnownFnValueSubstitution(proof),
    ) = &target.searched_proof else {
        panic!("both sides use the new branch");
    };
    assert_eq!(
        proof.cited_equal_fact_ids,
        vec![
            equality(&result.statement_results[3]).fact.fact_id,
            equality(&result.statement_results[4]).fact.fact_id
        ]
    );
}

#[test]
fn reverse_written_function_value_equations_are_cited() {
    let mut runtime = runtime();
    let result = verified(
        &mut runtime,
        "have fn shift(x R) R = x+3\nhave x R\nx+3=shift(x)\n2*shift(x)=2*x+6\n",
    );
    assert!(
        crate::json_output::project_stmt_detailed(&result.statement_results[3], &runtime)
            .stringify()
            .contains("KnownFnValueSubstitution")
    );
}

#[test]
fn false_goals_and_failed_statement_facts_do_not_publish() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn shift(x R) R = x+3\nhave x R\nshift(x)=x+3\n",
    );
    rejected(&mut runtime, "2*shift(x)=2*x+7\n");
    verified(&mut runtime, "2*shift(x)=2*x+6\n");
    rejected(&mut runtime, "2*shift(x)=2*x+7\n");
}

#[test]
fn discovery_of_definitions_nonfunction_aliases_and_invalid_domains_stays_off() {
    let mut runtime = runtime();
    verified(&mut runtime, "have fn shift(x R) R=x+3\nhave x R\n");
    rejected(&mut runtime, "2*shift(x)=2*x+6\n");
    verified(&mut runtime, "have a R=x+3\n");
    rejected(&mut runtime, "2*a=2*x+6\n");
    verified(&mut runtime, "have fn guarded(t R: t>0) R=t+3\n");
    let invalid = rejected(&mut runtime, "2*guarded(x)=2*x+6\n");
    let ExecStmtResult::Fact(crate::execute::ExecFactStmtResult::Failed(proof)) =
        &invalid.statement_results[0]
    else {
        panic!("failed guarded application");
    };
    assert!(proof.is_wd_failed());
}

#[test]
fn inserted_function_calls_do_not_start_a_second_substitution_or_definition() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn inner(x R) R=x+3\nhave fn outer(x R) R=inner(x)\nhave x R\nouter(x)=inner(x)\n",
    );
    rejected(&mut runtime, "2*outer(x)=2*x+6\n");
    verified(&mut runtime, "inner(x)=x+3\n");
    rejected(&mut runtime, "2*outer(x)=2*x+6\n");
    verified(&mut runtime, "2*outer(x)=2*inner(x)=2*(x+3)=2*x+6\n");
}

#[test]
fn ambiguous_direct_values_need_an_explicit_intermediate() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn shift(x R) R=x+3\nhave x R\nshift(x)=x+3\nshift(x)=3+x\n",
    );
    rejected(&mut runtime, "2*shift(x)=2*x+6\n");
    verified(&mut runtime, "2*shift(x)=2*(x+3)=2*x+6\n");
}

#[test]
fn local_value_equalities_do_not_escape_or_survive_a_failed_claim() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn shift(x R) R=x+3\nhave x R\nclaim:\n    ? 2*shift(x)=2*x+6\n    shift(x)=x+3\n",
    );
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("shift(x)=x+3", CodeSource::Eval)
        .unwrap();
    let mut parsed = runtime.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(value))) = parsed.remove(0) else {
        panic!("function value equation");
    };
    assert!(runtime
        .exact_property_equality_path(&value.left, &value.right)
        .is_none());
    // A successful claim publishes its conclusion, not its local source fact.
    verified(&mut runtime, "2*shift(x)=2*x+6\n");

    let mut fresh = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    verified(&mut fresh, "have fn shift(x R) R=x+3\nhave x R\n");
    rejected(
        &mut fresh,
        "claim:\n    ? 2*shift(x)=2*x+7\n    shift(x)=x+3\n",
    );
    rejected(&mut fresh, "2*shift(x)=2*x+6\n");
}

#[test]
fn restricted_truth_permissions_cannot_reenter_the_new_rewrite() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn shift(x R) R=x+3\nhave x R\nshift(x)=x+3\n",
    );
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("2*shift(x)=2*x+6", CodeSource::Eval)
        .unwrap();
    let mut parsed = runtime.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = parsed.remove(0) else {
        panic!("equality input")
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::BuiltinRule,
        VerifyStateLevel::Strategy,
        VerifyStateLevel::DefinitionAndForall,
    ] {
        assert!(runtime
            .verify_equal_fact(&fact, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(!runtime
        .verify_equal_fact(&fact, VerifyState::top_level())
        .unwrap()
        .is_failed());
}

#[test]
fn scalar_walk_does_not_rewrite_function_arguments_or_new_parents() {
    let mut runtime = runtime();
    verified(&mut runtime, "have fn inner(x R) R=x+3\nhave fn outer(x R) R=x+1\nhave x R\ninner(x)=x+3\nouter(x+3)=x+4\n");
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("outer(inner(x))+1=x+5", CodeSource::Eval)
        .unwrap();
    let mut parsed = runtime.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = parsed.remove(0) else {
        panic!("equality")
    };
    let mut citations = Vec::new();
    let rewritten = super::rewrite_known_fn_value_subterms(&runtime, &fact.left, &mut citations);
    assert_eq!(rewritten.ir(), fact.left.ir());
    assert!(citations.is_empty());
}
