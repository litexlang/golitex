use litex::output::display_stmt_result_json_v2;
use litex::prelude::*;
use std::rc::Rc;

#[test]
fn numeric_fact_json_v2_retains_normalization_store_and_infer() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("numeric_fact_json_v2");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("2 + 3 $in N", Rc::from("numeric_fact_json_v2.lit"))
        .expect("numeric membership tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("numeric membership parses");
    let result = runtime
        .execute_statement(&stmt)
        .expect("numeric membership verifies");

    let success = result
        .factual_success()
        .expect("numeric membership returns a factual success");

    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(fact_wd) = success
        .well_definedness
        .recursive
        .as_deref()
        .expect("fact execution owns its recursive WD result")
    else {
        panic!("numeric membership must use the atomic-fact WD layer");
    };
    assert_eq!(fact_wd.arguments.len(), 2);
    let SuccessVerifyObjWellDefinedResult::Direct(add_wd) = fact_wd.arguments[0].result.as_ref()
    else {
        panic!("the source expression must own a direct object WD result");
    };
    assert_eq!(add_wd.object.to_string(), "2 + 3");
    assert_eq!(add_wd.steps.children.len(), 2);
    assert_eq!(add_wd.steps.children[0].source_object.to_string(), "2");
    assert_eq!(add_wd.steps.children[1].source_object.to_string(), "3");
    assert_eq!(add_wd.steps.target_requirements.len(), 2);
    assert!(add_wd.steps.target_requirements.iter().all(|requirement| {
        matches!(
            requirement.verification.as_ref(),
            SuccessVerifyFactResult::AtomicFact(_)
        )
    }));
    assert!(matches!(
        fact_wd.arguments[1].result.as_ref(),
        SuccessVerifyObjWellDefinedResult::Direct(_)
    ));

    let SuccessFactProofResult::BuiltinRule(proof) = success.proof() else {
        panic!("closed numeric membership must retain its builtin proof");
    };
    let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = proof.evidence.typed()
    else {
        panic!("closed numeric membership must retain its evaluation evidence");
    };
    assert_eq!(evidence.evaluation.expression.to_string(), "2 + 3");
    assert_eq!(evidence.evaluation.value.to_string(), "5");
    let SuccessEvaluateObjStepResult::Binary(evaluation) = &evidence.evaluation.step else {
        panic!("2 + 3 must retain a binary evaluation layer");
    };
    assert_eq!(evaluation.operator, EvaluateBinaryObjOperator::Add);
    assert_eq!(evaluation.left.value.to_string(), "2");
    assert_eq!(evaluation.right.value.to_string(), "3");

    assert!(success.store.infers.store_fact_outputs[0].inferred_fact_ids[0].is_some());
    let application = success
        .store
        .infers
        .rule_applications
        .first()
        .expect("natural membership records its selected infer rule");
    assert_eq!(
        application.rule,
        InferRule::NaturalMembershipImpliesNonnegative
    );
    assert_eq!(application.premises.len(), 1);
    assert_eq!(application.conclusions.len(), 1);
    assert_eq!(
        application.premises[0].fact_id, success.store.fact_id,
        "the infer premise cites the stored source fact"
    );
    assert!(application.conclusions[0].fact_id.is_some());
    assert_ne!(
        application.conclusions[0].fact_id, success.store.fact_id,
        "source and inferred facts have distinct identities"
    );

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"schema\": \"litex.statement-result.v2\""));
    assert!(json.contains("\"kind\": \"Typed\""));
    assert!(json.contains("\"kind\": \"ClosedNumericMembership\""));
    assert!(json.contains("\"operator\": \"Add\""));
    assert!(json.contains("\"value\": \"5\""));
    assert!(json.contains("\"statement\": \"2 + 3 >= 0\""));
    assert!(json.contains("\"rule\": \"NaturalMembershipImpliesNonnegative\""));
    assert!(!json.contains("LegacyPassThrough"));
}

#[test]
fn refined_standard_set_infer_json_v2_retains_typed_source_carrier() {
    for (source, expected_rule, expected_set) in [
        (
            "1 $in R+",
            "PositiveStandardSetMembershipImpliesPositive",
            StandardSet::RPos,
        ),
        (
            "-1 $in R-",
            "NegativeStandardSetMembershipImpliesNegative",
            StandardSet::RNeg,
        ),
        (
            "1 $in C*",
            "NonzeroStandardSetMembershipImpliesNonzero",
            StandardSet::CStar,
        ),
    ] {
        let mut runtime = Runtime::new();
        runtime.start_isolated_source("refined_standard_set_infer_json_v2");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(source, Rc::from("refined_standard_set_infer_json_v2.lit"))
            .expect("refined standard-set membership tokenizes");
        let stmt = runtime
            .parse_statement(&mut blocks[0])
            .expect("refined standard-set membership parses");
        let result = runtime
            .execute_statement(&stmt)
            .expect("refined standard-set membership verifies");
        let fact = result
            .factual_success()
            .expect("refined standard-set membership is factual");
        let [application] = fact.store.infers.rule_applications.as_slice() else {
            panic!("{source} must retain exactly one typed inference application");
        };
        let retained_source_set = match &application.rule {
            InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => rule.source_set,
            InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => rule.source_set,
            InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => rule.source_set,
            other => panic!("{source} retained unexpected rule {other:?}"),
        };
        assert_eq!(retained_source_set, expected_set);

        let json = display_stmt_result_json_v2(&result);
        assert!(
            json.contains(&format!("\"rule\": \"{expected_rule}\"")),
            "{json}"
        );
        assert!(
            json.contains(&format!("\"source_set\": \"{expected_set}\"")),
            "{json}"
        );
    }
}

#[test]
fn object_choice_json_v2_retains_typed_standard_set_nonempty_child_evidence() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("object_choice_json_v2");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("have chosen R", Rc::from("object_choice_json_v2.lit"))
        .expect("object choice tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("object choice parses");
    let result = runtime
        .execute_statement(&stmt)
        .expect("object choice verifies");

    let StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(choice),
    )) = &result
    else {
        panic!("object choice returns its named result variant")
    };
    let nonempty = choice
        .verification
        .as_ref()
        .expect("object choice retains verification")
        .groups[0]
        .nonempty_check
        .as_deref()
        .expect("standard carrier retains nonempty child")
        .factual_success()
        .expect("nonempty child is factual");
    let SuccessFactProofResult::BuiltinRule(proof) = nonempty.proof() else {
        panic!("standard carrier nonempty child is builtin")
    };
    let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = proof.evidence.typed() else {
        panic!("standard carrier nonempty child retains typed evidence")
    };
    assert_eq!(evidence.target_set, StandardSet::R);
    assert_eq!(evidence.expected_target.to_string(), "$is_nonempty_set(R)");

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"StandardSetNonempty\""));
    assert!(json.contains("\"target_set\": \"R\""));
    assert!(json.contains("\"expected_target\": \"$is_nonempty_set(R)\""));
}

#[test]
fn claim_json_v2_serializes_named_verification_fields_and_children() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("claim_json_v2");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "claim:\n    ? 1 = 1\n    1 = 1",
            Rc::from("claim_json_v2.lit"),
        )
        .expect("claim tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("claim parses");
    let result = runtime.execute_statement(&stmt).expect("claim verifies");

    let StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
        claim,
    ))) = &result
    else {
        panic!("claim returns its matching successful statement result");
    };
    let Some(SuccessVerifyClaimResult::Fact(verification)) = &claim.verification else {
        panic!("ordinary claim owns its fact verification result");
    };
    assert_eq!(verification.proof_steps.len(), 1);
    assert_eq!(
        verification
            .conclusion_check
            .factual_success()
            .expect("claim conclusion is factual")
            .fact()
            .to_string(),
        "1 = 1"
    );

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"ClaimStmt\""));
    assert!(json.contains("\"kind\": \"SuccessVerifyClaimFactResult\""));
    assert!(json.contains("\"proof_steps\":"));
    assert!(json.contains("\"conclusion_check\":"));
    assert!(json.contains("\"kind\": \"AtomicFact\""));
}

#[test]
fn set_builder_wd_scope_is_owned_by_recursive_binder_fields() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("set_builder_recursive_wd");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "{x R: x > 0} = {x R: x > 0}",
            Rc::from("set_builder_recursive_wd.lit"),
        )
        .expect("set-builder equality tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("set-builder equality parses");
    let result = runtime
        .execute_statement(&stmt)
        .expect("set-builder equality verifies");

    let fact = result
        .factual_success()
        .expect("set-builder equality returns a fact result");
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
        .well_definedness
        .recursive
        .as_deref()
        .expect("fact owns recursive WD")
    else {
        panic!("set-builder equality uses atomic-fact WD");
    };
    assert_eq!(wd.arguments.len(), 2);
    for argument in &wd.arguments {
        let SuccessVerifyObjWellDefinedResult::Direct(object_wd) = argument.result.as_ref() else {
            panic!("each set-builder occurrence owns a direct WD node");
        };
        let Some(binder) = object_wd.steps.binder.as_deref() else {
            panic!("set-builder WD owns its binder result as a nested field");
        };
        let SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(binder) = binder else {
            panic!("set-builder object must own a set-builder binder result");
        };
        assert_eq!(binder.parameter_carrier.source_object.to_string(), "R");
        assert_eq!(binder.conditions.len(), 1);
        let Fact::AtomicFact(AtomicFact::InFact(parameter_membership)) =
            &binder.parameter.proposition
        else {
            panic!("set-builder parameter premise is membership");
        };
        let Fact::AtomicFact(AtomicFact::GreaterFact(condition)) = &binder.conditions[0].store.fact
        else {
            panic!("set-builder condition retains its greater-than fact");
        };
        assert!(objs_equal_with_nested_binder_alpha_equivalence(
            &parameter_membership.element,
            &condition.left,
        ));
        assert!(binder.conditions[0].store.fact_id.is_some());
    }

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"SetBuilder\""));
    assert!(!json.contains("ambient_scope"));
    assert!(!json.contains("LegacyPassThrough"));
}

#[test]
fn anonymous_function_wd_keeps_each_body_inside_its_own_binder_result() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("anonymous_function_recursive_wd");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "fn(x R) R {x + 1} = fn(y R) R {y + 1}",
            Rc::from("anonymous_function_recursive_wd.lit"),
        )
        .expect("anonymous-function equality tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("anonymous-function equality parses");
    let result = runtime
        .execute_statement(&stmt)
        .expect("alpha-equivalent anonymous functions verify");
    let fact = result.factual_success().expect("result is factual");
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
        .well_definedness
        .recursive
        .as_deref()
        .expect("fact owns recursive WD")
    else {
        panic!("function equality uses atomic-fact WD");
    };
    assert_eq!(wd.arguments.len(), 2);
    let mut binder_addresses = Vec::new();
    for argument in &wd.arguments {
        let SuccessVerifyObjWellDefinedResult::Direct(object_wd) = argument.result.as_ref() else {
            panic!("each anonymous-function occurrence owns direct WD");
        };
        let Some(binder) = object_wd.steps.binder.as_deref() else {
            panic!("anonymous-function WD owns its binder subtree");
        };
        binder_addresses.push(binder as *const _ as usize);
        let SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(binder) = binder else {
            panic!("anonymous function owns the matching binder result");
        };
        assert_eq!(binder.parameters.len(), 1);
        assert_eq!(binder.parameter_carriers[0].source_object.to_string(), "R");
        let Fact::AtomicFact(AtomicFact::InFact(parameter_membership)) =
            &binder.parameters[0].proposition
        else {
            panic!("anonymous-function parameter premise is membership");
        };
        let Obj::Add(body) = &binder.body.source_object else {
            panic!("anonymous-function body retains its addition object");
        };
        assert!(objs_equal_with_nested_binder_alpha_equivalence(
            &parameter_membership.element,
            &body.left,
        ));
        let Fact::AtomicFact(AtomicFact::InFact(body_membership)) =
            &binder.body_membership.expected_proposition
        else {
            panic!("anonymous-function body obligation is membership");
        };
        assert!(objs_equal_with_nested_binder_alpha_equivalence(
            &body_membership.element,
            &binder.body.source_object,
        ));
        assert_eq!(body_membership.set.to_string(), "R");
    }
    assert_ne!(binder_addresses[0], binder_addresses[1]);

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"AnonymousFunction\""));
    assert!(!json.contains("ambient_scope"));
    assert!(!json.contains("LegacyPassThrough"));
}

#[test]
fn forall_wd_returns_binder_premise_and_conclusion_layers() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("forall_recursive_wd");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "forall x R:\n    x >= 0\n    =>:\n        x = x",
            Rc::from("forall_recursive_wd.lit"),
        )
        .expect("forall tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("forall parses");
    let result = runtime.execute_statement(&stmt).expect("forall verifies");
    let fact = result.factual_success().expect("result is factual");
    let SuccessVerifyFactWellDefinedProofResult::ForallFact(wd) = fact
        .well_definedness
        .recursive
        .as_deref()
        .expect("forall owns recursive WD")
    else {
        panic!("forall statement owns a forall WD result");
    };
    assert_eq!(wd.binder.parameter_groups.len(), 1);
    assert_eq!(wd.binder.parameter_groups[0].parameters.len(), 1);
    assert_eq!(wd.premises.len(), 1);
    assert_eq!(wd.conclusions.len(), 1);
    assert!(wd.premises[0].store.fact_id.is_some());
    assert!(wd.conclusions[0].store.fact_id.is_some());
    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"ForallFact\""));
    assert!(json.contains("\"kind\": \"SuccessVerifyFactBinderResult\""));
    assert!(!json.contains("ambient_scope"));
    assert!(!json.contains("LegacyPassThrough"));
}

#[test]
fn partial_predicate_wd_retains_its_domain_proof_result() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("partial_predicate_recursive_wd");
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("$prime(2)", Rc::from("partial_predicate_recursive_wd.lit"))
        .expect("prime fact tokenizes");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("prime fact parses");
    let result = runtime
        .execute_statement(&stmt)
        .expect("prime fact verifies");
    let fact = result.factual_success().expect("result is factual");
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
        .well_definedness
        .recursive
        .as_deref()
        .expect("prime fact owns recursive WD")
    else {
        panic!("prime statement owns atomic WD");
    };
    assert_eq!(wd.predicate.name, PRIME);
    assert_eq!(wd.predicate.expected_arity, 1);
    assert_eq!(wd.predicate.domain_checks.len(), 1);
    assert_eq!(
        wd.predicate.domain_checks[0].role,
        AtomicPredicateDomainCheckRole::PrimeNaturalArgument
    );
    assert_eq!(
        wd.predicate.domain_checks[0]
            .result
            .factual_success()
            .expect("prime domain check is factual")
            .fact()
            .to_string(),
        "2 $in N"
    );

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"kind\": \"SuccessVerifyAtomicPredicateWellDefinedResult\""));
    assert!(json.contains("\"role\": \"PrimeNaturalArgument\""));
}
