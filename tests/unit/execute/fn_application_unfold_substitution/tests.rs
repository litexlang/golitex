use crate::prelude::*;

const AFFINE: &str = "have fn shift(x R) R = x + 3\nhave x R\n2 * shift(x) = 2 * x + 6\n";

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

fn unfold(
    statement: &ExecStmtResult,
) -> &super::FnApplicationUnfoldSubstitutionBuiltinRewriteProof {
    let EqualFactSearchedProof::ByBuiltinRewrite(
        super::super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(proof),
    ) = &equality(statement).searched_proof else { panic!("function-head equality rewrite must win") };
    proof
}

fn parse_equal(runtime: &mut Runtime, source: &str) -> EqualFact {
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize(source, CodeSource::Eval)
        .unwrap();
    let mut parsed = runtime.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = parsed.remove(0) else {
        panic!("equality")
    };
    fact
}

#[test]
fn have_fn_equal_publishes_both_exact_special_properties() {
    let mut runtime = runtime();
    let result = verified(&mut runtime, "have fn f(x N) N=x+1");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        crate::execute::ExecHaveFnEqualStmtResult::Success(p),
    )) = &result.statement_results[0]
    else {
        panic!("definition")
    };
    let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = runtime
        .fact_by_id_in_stack(p.store_and_infer_result.defining_equal_fact_id)
        .unwrap()
    else {
        panic!("definition equality")
    };
    assert!(matches!(
        eq.right,
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))
    ));
    let properties = runtime.known_special_properties_of(&eq.left);
    assert!(properties
        .iter()
        .any(|v| matches!(v, crate::exec_env::SpecialProperty::Equality(e) if e == eq)));
    assert!(properties
        .iter()
        .any(|v| matches!(v, crate::exec_env::SpecialProperty::Membership(_))));
    assert!(p
        .store_and_infer_result
        .stored_fact_ids
        .contains(&eq.fact_id));
}

#[test]
fn natural_number_tracer_and_reciprocal_are_direct() {
    let mut runtime = runtime();
    let result = verified(&mut runtime, include_str!("../../../../examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution.lit"));
    let detail =
        crate::json_output::project_run_detailed(&result, &runtime, "test", None).stringify();
    assert!(detail.contains("FnApplicationUnfoldSubstitution"));
    assert!(detail.contains("function_equal") && detail.contains("body_application_well_defined"));
}

#[test]
fn forall_premise_supplies_anonymous_function_body_without_definition() {
    let mut runtime = runtime();
    let result = verified(
        &mut runtime,
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution_forall_equality.lit"),
    );
    assert_eq!(result.statement_results.len(), 1);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &result.statement_results[0]
    else {
        panic!("universal fact, not a function declaration")
    };
    let VerifyFactResult::ForallFact(result) = &statement.verify_result else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        result.as_ref()
    else {
        panic!("local universal scope")
    };
    let VerifyFactResult::Equality(result) = &forall.proved_then_facts[0].verify_result else {
        panic!("conclusion equality")
    };
    let VerifyEqualityResult::Success(equal) = result.as_ref() else {
        panic!("verified conclusion")
    };
    let EqualFactSearchedProof::ByBuiltinRewrite(
        super::super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(proof),
    ) = &equal.searched_proof else {
        panic!("anonymous-function equality substitution")
    };
    assert_eq!(proof.expansions.len(), 1);
    let super::FunctionBodySourceProof::KnownEquality(path) = &proof.expansions[0].function_body
    else {
        panic!("stored function-head equality")
    };
    assert_eq!(path.path.len(), 1);
    let (head, anonymous_function, cite_id) = &path.path[0];
    assert!(forall.assumed_dom_facts[0]
        .store_and_infer
        .stored_fact_ids()
        .contains(cite_id));
    let Some(Fact::AtomicFact(AtomicFact::EqualFact(source))) =
        forall.local_env.facts.facts_by_id.get(cite_id)
    else {
        panic!("binder-local equality citation")
    };
    assert_eq!(source.left.ir(), head.ir());
    assert_eq!(source.right.ir(), anonymous_function.ir());
    assert!(matches!(
        anonymous_function,
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))
    ));
}

#[test]
fn forall_function_membership_without_body_equality_still_misses() {
    let mut runtime = runtime();
    verified(&mut runtime, "have retained_point R=2");
    rejected(
        &mut runtime,
        "forall f fn(t R: t>0) R, x R:\n    x>0\n    =>:\n        2*f(x)=2*x",
    );
    verified(&mut runtime, "retained_point=2");
}

#[test]
fn forall_anonymous_function_equality_does_not_remove_application_guard() {
    let mut runtime = runtime();
    let result = rejected(
        &mut runtime,
        "forall f fn(t R: t>0) R, x R:\n    f=fn(t R: t>0) R {t}\n    =>:\n        2*f(x)=2*x",
    );
    let ExecStmtResult::Fact(ExecFactStmtResult::Failed(statement)) = &result.statement_results[0]
    else {
        panic!("failed universal fact")
    };
    let VerifyFactResult::ForallFact(result) = statement else {
        panic!("forall failure")
    };
    let VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
        failed_then,
        ..
    }) = result.as_ref()
    else {
        panic!("failed conclusion")
    };
    assert!(failed_then.is_wd_failed());
}

#[test]
fn affine_retains_definition_citation_and_checked_residual() {
    let mut runtime = runtime();
    let result = verified(&mut runtime, AFFINE);
    let proof = unfold(&result.statement_results[2]);
    assert_eq!(proof.expansions.len(), 1);
    let super::FunctionBodySourceProof::KnownEquality(path) = &proof.expansions[0].function_body
    else {
        panic!("exact source")
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        crate::execute::ExecHaveFnEqualStmtResult::Success(def),
    )) = &result.statement_results[0]
    else {
        panic!("definition")
    };
    assert_eq!(
        path.path[0].2,
        def.store_and_infer_result.defining_equal_fact_id
    );
    let VerifyFactResult::Equality(residual) = &proof.residual_equal else {
        panic!("residual")
    };
    let VerifyEqualityResult::Success(residual) = residual.as_ref() else {
        panic!("checked residual")
    };
    assert_eq!(residual.fact.left.ir(), proof.rewritten_left.ir());
    assert_eq!(residual.fact.right.ir(), proof.rewritten_right.ir());
    assert!(matches!(
        residual.searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(_)
    ));
}

#[test]
fn both_sides_and_repeated_original_calls_are_all_recorded() {
    let mut runtime = runtime();
    let result = verified(
        &mut runtime,
        "have fn left(t R) R=t+1\nhave fn right(t R) R=t-1\nhave x R\nleft(x)+left(x)=2*right(x)+4",
    );
    let proof = unfold(&result.statement_results[3]);
    assert_eq!(proof.expansions.len(), 3);
    assert_eq!(
        proof.expansions[0].application.ir(),
        proof.expansions[1].application.ir()
    );
    assert_ne!(
        proof.expansions[0].application.ir(),
        proof.expansions[2].application.ir()
    );
}

#[test]
fn stored_application_values_do_not_choose_the_definition_body() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn shift(t R) R=t+3\nhave x R\nshift(x)=x+3\nshift(x)=3+x",
    );
    let result = verified(&mut runtime, "2*shift(x)=2*x+6");
    assert_eq!(unfold(&result.statement_results[0]).expansions.len(), 1);
}

#[test]
fn anonymous_function_aliases_share_the_head_equality_path() {
    let mut runtime = runtime();
    let result = verified(
        &mut runtime,
        "let f=fn(t R) R {t+1}\nhave x R\n2*f(x)=2*x+2",
    );
    assert_eq!(unfold(&result.statement_results[2]).expansions.len(), 1);
}

#[test]
fn arguments_are_instantiated_by_binder_identity() {
    let mut runtime = runtime();
    verified(&mut runtime, "have fn mix(s,t R) R=s+2*t\nhave x,y R");
    verified(&mut runtime, "2*mix(y,x)=2*y+4*x");
    rejected(&mut runtime, "2*mix(x,y)=2*y+4*x");
    let result = verified(&mut runtime, "2*mix(x,y)-mix(y,x)=3*y");
    assert_eq!(unfold(&result.statement_results[0]).expansions.len(), 2);
}

#[test]
fn false_conclusions_do_not_publish_and_session_remains_live() {
    let mut runtime = runtime();
    verified(&mut runtime, "have fn f(t N) N=t+1\nhave x N");
    for _ in 0..2 {
        let before = runtime.top_exec_env().facts.facts_by_id.len();
        let failed = rejected(&mut runtime, "2*f(x)=2*x+3");
        assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), before);
        let projected =
            crate::json_output::project_stmt_normal(&failed.statement_results[0], &runtime)
                .stringify();
        assert!(projected.contains("search_proof"));
        verified(&mut runtime, "1=1");
    }
    verified(&mut runtime, "2*f(x)=2*x+2");
}

#[test]
fn missing_guard_and_invalid_domain_remain_wd_failures() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn guarded(t R: t>0) R=t+3\nhave x R\nhave fn natural(t N) N=t+1",
    );
    for source in [
        "2*guarded(x)=2*x+6",
        "2*natural(-1)=0",
        "2*guarded(x)/0=(2*x+6)/0",
        "2*natural(1,2)=4",
    ] {
        let result = rejected(&mut runtime, source);
        let ExecStmtResult::Fact(crate::execute::ExecFactStmtResult::Failed(p)) =
            &result.statement_results[0]
        else {
            panic!("WD failed")
        };
        assert!(p.is_wd_failed(), "{source}");
    }
    verified(
        &mut runtime,
        "forall y R:\n    y>0\n    =>:\n        2*guarded(y)=2*y+6",
    );
}

#[test]
fn membership_only_has_no_body_to_unfold() {
    let mut runtime = runtime();
    verified(&mut runtime, "have f fn(t R) R\nhave x R");
    rejected(&mut runtime, "2*f(x)=2*x+2");
}

#[test]
fn inserted_bodies_are_not_unfolded_again() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn inner(t R) R=t+3\nhave fn outer(t R) R=inner(t)\nhave x R",
    );
    rejected(&mut runtime, "2*outer(x)=2*x+6");
    verified(&mut runtime, "2*outer(x)=2*inner(x)=2*(x+3)=2*x+6");
}

#[test]
fn outermost_call_unfolds_without_visiting_its_arguments() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn inner(t R) R=t+3\nhave fn outer(t R) R=t+1\nhave x R",
    );
    let fact = parse_equal(&mut runtime, "2*outer(inner(x))=2*(inner(x)+1)");
    let mut steps = Vec::new();
    let rewritten = super::rewrite_fn_equal_to_anonymous_function_subterms(
        &mut runtime,
        &fact.left,
        VerifyState::top_level(),
        &mut steps,
    )
    .unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(rewritten.ir(), fact.right.ir());
    rejected(&mut runtime, "2*outer(inner(x))=2*x+8");
    verified(&mut runtime, "2*outer(inner(x))=2*(inner(x)+1)");
}

#[test]
fn function_value_equalities_are_not_synthetically_stored() {
    let mut runtime = runtime();
    verified(&mut runtime, AFFINE);
    let eq = parse_equal(&mut runtime, "shift(x)=x+3");
    assert!(runtime
        .exact_property_equality_path(&eq.left, &eq.right)
        .is_none());
}

#[test]
fn failed_claim_discards_local_function_and_its_properties() {
    let mut runtime = runtime();
    verified(&mut runtime, "have x R");
    let before_facts = runtime.top_exec_env().facts.facts_by_id.len();
    let before_properties = runtime.top_exec_env().special_properties.len();
    rejected(
        &mut runtime,
        "claim:\n    ? x=x+1\n    have fn local(t R) R=t+1\n    2*local(x)=2*x+2",
    );
    assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), before_facts);
    assert_eq!(
        runtime.top_exec_env().special_properties.len(),
        before_properties
    );
    verified(&mut runtime, "1=1");
}

#[test]
fn restricted_truth_permissions_do_not_restore_rewrite() {
    let mut runtime = runtime();
    verified(&mut runtime, "have fn f(t R) R=t+1\nhave x R");
    let fact = parse_equal(&mut runtime, "2*f(x)=2*x+2");
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
fn scalar_matrix_checks_carriers_and_false_neighbors_without_value_seeds() {
    for carrier in ["N", "R", "Q", "Z", "C"] {
        for offset in [1, 2, 3] {
            let mut runtime = runtime();
            verified(
                &mut runtime,
                &format!("have fn f(t {carrier}) {carrier}=t+{offset}\nhave x {carrier}"),
            );
            let result = verified(&mut runtime, &format!("2*f(x)=2*x+{}", 2 * offset));
            unfold(&result.statement_results[0]);
            rejected(&mut runtime, &format!("2*f(x)=2*x+{}", 2 * offset + 1));
        }
    }
}

#[test]
fn evidence_projects_in_all_output_languages() {
    for language in OutputLanguage::ALL {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: true,
            strict: true,
            language,
        });
        let result = verified(&mut runtime, AFFINE);
        assert!(
            crate::json_output::project_stmt_detailed(&result.statement_results[2], &runtime)
                .stringify()
                .contains("FnApplicationUnfoldSubstitution")
        );
        crate::json_output::project_stmt_normal(&result.statement_results[2], &runtime);
    }
}

#[test]
fn run_examples_fn_application_unfold_substitution_positive_corpus() {
    for suffix in [
        "",
        "_multiple_calls",
        "_scalar_arithmetic",
        "_exact_arguments",
        "_guarded",
        "_duplicate_sources",
        "_forall_equality",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution{suffix}.lit"));
        let mut runtime = runtime();
        verified(&mut runtime, &std::fs::read_to_string(path).unwrap());
    }
}

#[test]
fn run_examples_fn_application_unfold_substitution_negative_manifest() {
    use crate::knowledge_base::JsonValue;
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/negative/fn_application_unfold_substitution");
    let manifest = JsonValue::parse(include_str!(
        "../../../../examples/negative/fn_application_unfold_substitution/manifest.json"
    ))
    .unwrap();
    for entry in manifest.as_array().unwrap() {
        let e = entry.as_object().unwrap();
        let source =
            std::fs::read_to_string(directory.join(e.get("file").unwrap().as_str().unwrap()))
                .unwrap();
        let (prefix, target) = source.trim_end().rsplit_once('\n').unwrap();
        let mut runtime = runtime();
        verified(&mut runtime, prefix);
        for _ in 0..2 {
            let before = runtime.top_exec_env().facts.facts_by_id.len();
            let result = rejected(&mut runtime, target);
            let p = crate::json_output::project_stmt_normal(&result.statement_results[0], &runtime);
            let fields = p.as_object().unwrap();
            assert_eq!(
                fields
                    .get("why_failed")
                    .unwrap()
                    .as_object()
                    .unwrap()
                    .get("phase")
                    .unwrap()
                    .as_str()
                    .unwrap(),
                e.get("expected_phase").unwrap().as_str().unwrap()
            );
            for k in ["stores", "infers"] {
                assert!(fields.get(k).unwrap().as_array().unwrap().is_empty());
            }
            assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), before);
            verified(&mut runtime, "1=1");
        }
    }
}

#[test]
fn selected_body_guard_cannot_be_hidden_by_a_weaker_signature() {
    let mut runtime = runtime();
    rejected(
        &mut runtime,
        "forall f fn(t R) R,x R:\n    f=fn(t R: t>0) R {t+1}\n    =>:\n        2*f(x)=2*x+2",
    );
    verified(&mut runtime, "forall f fn(t R) R,x R:\n    f=fn(t R: t>0) R {t+1}\n    x>0\n    =>:\n        2*f(x)=2*x+2");
}

#[test]
fn reversed_direct_head_equalities_work_without_equality_graph_walks() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "forall f fn(t R) R,x R:\n    fn(t R) R {t+1}=f\n    =>:\n        2*f(x)=2*x+2",
    );
    rejected(
        &mut runtime,
        "forall f,g fn(t R) R,x R:\n    f=g\n    g=fn(t R) R {t+1}\n    =>:\n        2*f(x)=2*x+2",
    );
}

#[test]
fn reversed_explicit_beta_endpoint_stays_checkable() {
    let mut runtime = runtime();
    verified(
        &mut runtime,
        "have fn inner(t R) R=t+3\nhave fn outer(t R) R=inner(t)\nhave x R",
    );
    let result = verified(&mut runtime, "2*inner(x)=2*outer(x)");
    let p = unfold(&result.statement_results[0]);
    assert_eq!(p.expansions.len(), 1);
    assert!(p.expansions[0]
        .application
        .readable_string()
        .contains("outer"));
}
