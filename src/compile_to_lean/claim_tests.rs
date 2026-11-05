use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const PLAIN: &str = "claim:\n    ? 1 = 1\n    1 = 1\n1 = 1\n";
const FORALL: &str = "claim:\n    ? forall x R:\n        x != 0\n        =>:\n            x / x = 1\n    x / x = 1\n";
const NESTED_TUPLE_CASES: &str = r#"thm contextual_tuple_case_publication:
    ? forall n,cutoff N+:
        n>cutoff
        cart({k N+:k>=cutoff},{k N+:k>=cutoff}) $subset {p cart(N+,N+):p(1)>=cutoff}
        =>:
            n>=cutoff
    claim:
        ? n>=cutoff
        by cases:
            ? n>=cutoff
            case n<=cutoff:
                impossible n<=cutoff
            case n>cutoff:
                n $in {k N+:k>=cutoff}
                cutoff $in {k N+:k>=cutoff}
                (n,cutoff) $in cart({k N+:k>=cutoff},{k N+:k>=cutoff})
                (n,cutoff) $in {p cart(N+,N+):p(1)>=cutoff}
                n>=cutoff

thm contextual_tuple_case_function_condition:
    ? forall a seq(R),cutoff N+:
        cart({k N+:k>=cutoff},{k N+:k>=cutoff}) $subset {p cart(N+,N+):a(p(1))=a(p(1))}
        =>:
            cutoff=cutoff
    claim:
        ? forall n N+:
            a(n)=a(n)
        claim:
            ? a(n)=a(n)
            by cases:
                ? a(n)=a(n)
                case n<=cutoff:
                    a(n)=a(n)
                case n>cutoff:
                    n $in {k N+:k>=cutoff}
                    cutoff $in {k N+:k>=cutoff}
                    (n,cutoff) $in cart({k N+:k>=cutoff},{k N+:k>=cutoff})
                    (n,cutoff) $in {p cart(N+,N+):a(p(1))=a(p(1))}
                    a(n)=a(n)
    cutoff=cutoff


"#;

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

#[test]
fn local_theorem_calls_accept_constructed_and_enclosing_generic_sequences() {
    let source = "claim:\n    ? forall a seq(R):\n        a=a\n    prop local_sequence_self(x seq(R)):\n        x=x\n    thm local_sequence_copy:\n        ? forall x seq(R):\n            $local_sequence_self(x)\n        by def $local_sequence_self(x)\n    have fn b(n N+) R=0\n    release thm local_sequence_copy(b)\n    release thm local_sequence_copy(a)\n    a=a\n";
    for source in [
        source.to_owned(),
        source.replace(
            "release thm local_sequence_copy(a)",
            "by thm local_sequence_copy(a) => $local_sequence_self(a)",
        ),
    ] {
        let (result, compiler) = checked(&source);
        let output = compiler
            .compile_run(&result, "local_theorem_hosts")
            .expect("both explicit invocation routes reuse the same local theorem");
        assert!(output.contains("let _local_theorem_argument_0 :="));
    }
}

#[test]
fn local_predicate_captures_retain_the_source_and_accept_distinct_host_representations() {
    let source = "claim:\n    ? 0=0\n    prop local_real_self(x R):\n        x=x\n    by def $local_real_self(0)\n    claim:\n        ? forall a seq(R),n N+:\n            $local_real_self(a(n))\n        by def $local_real_self(a(n))\n    0=0\n";
    let (mut result, compiler) = checked(source);
    compiler
        .compile_run(&result, "local_predicate_hosts")
        .expect("the same local predicate accepts literal and certified call values");
    let outer = claim_mut(&mut result.statement_results[0]);
    let ExecClaimBodyProof::NonForall(body) = &mut outer.body else {
        panic!("plain outer claim");
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(declaration),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original local predicate declaration");
    };
    declaration.statement.name.push_str("_changed");
    assert_eq!(
        compiler
            .compile_run(&result, "changed_local_predicate")
            .unwrap_err()
            .route,
        "Theorem/ProofStepCapture"
    );
}

#[test]
fn nested_claim_goals_retain_their_original_function_call_constructors() {
    let (result, compiler) = checked(NESTED_TUPLE_CASES);
    if let Err(error) = compiler.compile_run(&result, "nested_tuple_claim_formation") {
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            crate::execute::ExecDefThmStmtResult::Success(theorem),
        )) = &result.statement_results[1]
        else {
            panic!()
        };
        let crate::execute::ExecDefThmBodyProof::Forall(body) = &theorem.body else {
            panic!()
        };
        let claim = claim(&body.proof_steps[0]);
        let VerifyFactWellDefinedResult::Success(goal_wd) = &claim.goal_wd else {
            panic!()
        };
        let FactWellDefinedProof::ForallFact(forall) = goal_wd else {
            panic!()
        };
        if let FactWellDefinedProof::Equality(equality) = &forall.detailed_ref().then[0] {
            for (label, wd) in [
                ("left", &equality.detailed_ref().left),
                ("right", &equality.detailed_ref().right),
            ] {
                let kind = match wd.detailed_ref() {
                    DetailedObjWellDefinedProof::ByDef { .. } => "original constructor",
                    DetailedObjWellDefinedProof::ByKnown { .. } => "cached reference",
                };
                eprintln!("ORIGINAL CLAIM {label}: {kind}, {}", wd.obj().ir());
            }
        }
        let Fact::ForallFact(fact) = &theorem.statement.fact else {
            panic!()
        };
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let parent = SourcePosition::new(
            Some(&root),
            SourceOwner::Named(theorem),
            fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len(),
        );
        eprintln!(
            "INITIAL CLAIM WD: {:?}",
            compiler.compile_fact_wd(goal_wd, &claim.statement.fact, &parent)
        );
        panic!("goal formation keeps original call bindings while nested cases replay: {error}");
    }
}

#[test]
fn completed_plain_proofs_retain_only_caller_owned_goal_formation() {
    for declaration in ["claim:", "thm caller_abs:"] {
        let source =
            format!("have a R\n{declaration}\n    ? abs(a)>=0\n    abs(a)>=0\nabs(a)>=0\n");
        let (result, compiler) = checked(&source);
        let goal = match &result.statement_results[1] {
            ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
                ExecClaimStmtResult::Success(proof),
            )) => &proof.goal_wd,
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                crate::execute::ExecDefThmStmtResult::Success(proof),
            )) => &proof.goal_wd,
            _ => panic!("completed plain proof"),
        };
        let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::AtomicExceptEquality(wd)) =
            goal
        else {
            panic!("original goal formation");
        };
        let object = wd.detailed_ref().well_defined_of_each_parameter[0].obj();
        let before = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        assert!(compiler.compile_object_reference(object, &before).is_err());
        let after = SourcePosition {
            before: 2,
            ..before
        };
        compiler.compile_object_reference(object, &after).unwrap();
        compiler
            .compile_run(&result, "caller_owned_goal_formation")
            .unwrap();
    }
    let (result, compiler) = checked(FORALL);
    let proof = claim(&result.statement_results[0]);
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)) = &proof.goal_wd
    else {
        panic!("quantified goal formation");
    };
    let FactWellDefinedProof::Equality(wd) = &wd.detailed_ref().then[0] else {
        panic!("original dependent division");
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(compiler
        .compile_object_reference(wd.detailed_ref().left.obj(), &outside)
        .is_err());
}

#[test]
fn existential_returns_retain_outer_formation_before_any_hypothetical_witness() {
    let source = "thm caller_tail:\n    ? forall a seq(R),L R,epsilon R+:\n        $has_seq_limsup(a,L)\n        =>:\n            epsilon=epsilon\n    release thm seq_limsup_bound(a,L,epsilon)\n    obtain U0 from exist cutoff N+ st {{n N+:n>=cutoff} $subset preimage_set(a,{v R:v<L+epsilon})}\n    epsilon=epsilon\n";
    let (result, compiler) = checked(source);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        crate::execute::ExecDefThmStmtResult::Success(theorem),
    )) = &result.statement_results[0]
    else {
        panic!("original theorem");
    };
    let Fact::ForallFact(fact) = &theorem.statement.fact else {
        panic!("forall goal");
    };
    let crate::execute::ExecDefThmBodyProof::Forall(body) = &theorem.body else {
        panic!("forall body");
    };
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::Thm(
        crate::execute::execute_by_stmt::ExecReleaseThmStmtResult::Success(release),
    )) = &body.proof_steps[0]
    else {
        panic!("original release");
    };
    let FactWellDefinedProof::ExistFact(formation) = &release.stored_wd[0] else {
        panic!("returned existential formation");
    };
    let FactWellDefinedProof::AtomicExceptEquality(subset) =
        &formation.detailed_ref().assumed_body_facts[0].well_defined
    else {
        panic!("original subset formation");
    };
    let objects = &subset.detailed_ref().well_defined_of_each_parameter;
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let head = fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len();
    let before = SourcePosition::new(Some(&root), SourceOwner::Named(theorem), head);
    assert!(compiler
        .compile_object_reference(objects[1].obj(), &before)
        .is_err());
    let after = SourcePosition {
        before: head + 1,
        ..before
    };
    compiler
        .compile_object_reference(objects[1].obj(), &after)
        .unwrap();
    assert!(compiler
        .compile_object_reference(objects[0].obj(), &after)
        .is_err());
    let witness = formation
        .detailed_ref()
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    assert!(after
        .with_visible_wd(objects[1].obj(), &mut |_, producer| {
            assert!(producer.visible_fact(witness, &compiler.runtime).is_err());
            Ok(())
        })
        .unwrap()
        .is_some());
    compiler
        .compile_run(&result, "caller_owned_existential_formation")
        .unwrap();
}

#[test]
fn original_claim_formation_supplies_constructors_without_assuming_its_goal() {
    let (result, compiler) = checked(FORALL);
    let proof = claim(&result.statement_results[0]);
    let Fact::ForallFact(fact) = &proof.statement.fact else {
        panic!()
    };
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(goal)) = &fact.then_facts[0]
    else {
        panic!()
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let before = SourcePosition::new(Some(&root), SourceOwner::Claim(proof), 0);
    assert!(compiler
        .compile_object_reference(&goal.left, &before)
        .is_err());
    let body = SourcePosition {
        before: fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len(),
        ..before
    };
    assert!(compiler.compile_object_reference(&goal.left, &body).is_ok());
    assert!(body.visible_fact(goal.fact_id, &compiler.runtime).is_err());
    assert!(body.visible_fact(fact.fact_id, &compiler.runtime).is_err());
}

fn claim(statement: &ExecStmtResult) -> &ExecClaimStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = statement
    else {
        panic!("successful claim result");
    };
    claim
}

fn claim_mut(statement: &mut ExecStmtResult) -> &mut ExecClaimStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = statement
    else {
        panic!("successful claim result");
    };
    claim
}

fn forall_mut(
    claim: &mut ExecClaimStmtSuccess,
) -> &mut crate::execute::execute_proof_block_stmt::ExecClaimForallProof {
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall body");
    };
    body
}

#[test]
fn plain_claim_replays_body_conclusion_and_parent_store() {
    let (result, compiler) = checked(PLAIN);
    let claim = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::NonForall(body) = &claim.body else {
        panic!("direct goal body");
    };
    assert_eq!(body.proof_steps.len(), claim.statement.proof.len());
    assert_eq!(
        claim.stored.primary_fact_id(),
        claim.statement.fact.fact_id()
    );
    let lean = compiler
        .compile_run(&result, "plain_claim")
        .expect("claim replay");
    assert!(lean.contains(&format!(
        "theorem h_{}",
        claim.statement.fact.fact_id().value()
    )));
    assert!(!lean.contains("sorry"));
}

#[test]
fn forall_claim_captures_distinct_original_and_body_headers() {
    let (result, compiler) = checked(FORALL);
    let claim = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &claim.body else {
        panic!("forall body");
    };
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
        &claim.goal_wd
    else {
        panic!("original goal formation");
    };
    assert_eq!(
        body.introduced_params
            .defined_params
            .store_and_infer_results
            .len(),
        1
    );
    assert_eq!(body.assumed_dom_facts.len(), 1);
    assert_ne!(
        goal.detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
        body.introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
    );
    compiler
        .compile_run(&result, "forall_claim")
        .expect("both captured headers replay");
}

#[test]
fn claim_replays_body_local_have_without_exporting_its_identifier() {
    let source = "claim:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    compiler
        .compile_run(&result, "claim_local_have")
        .expect("ordered local producer replay");
}

#[test]
fn named_route_replays_the_same_real_parameter_alias_capture() {
    let source = "thm alias_claim_comparison:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    compiler
        .compile_run(&result, "named_real_parameter_alias")
        .expect("the same shared numeric WD route has its actual R header certificate");
}

#[test]
fn claim_local_alias_identifier_cannot_be_seen_early_or_escape_after_store() {
    let source = "claim:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    let proof = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &proof.body else {
        panic!("actual forall body")
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(alias)),
    )) = &body.proof_steps[0]
    else {
        panic!("actual typed alias producer")
    };
    let object = Obj::Identifier(IdentifierObj::from_bound_name(
        &alias.statement.param_def.groups[0].params[0],
    ));
    let original = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let early = SourcePosition::new(Some(&original), SourceOwner::Claim(proof), 1);
    assert_eq!(
        compiler
            .compile_object_reference(&object, &early)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
    let completed_alias = SourcePosition { before: 2, ..early };
    assert!(compiler
        .compile_object_reference(&object, &completed_alias)
        .is_ok());
    let closed = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert_eq!(
        compiler
            .compile_object_reference(&object, &closed)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
}

#[test]
fn claim_cursor_rejects_future_body_fact_and_seals_helper_after_store() {
    let (result, compiler) = checked(FORALL);
    let proof = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &proof.body else {
        panic!("forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &body.proof_steps[0] else {
        panic!("actual body fact");
    };
    let helper = step.store_and_infer_result.primary_fact_id();
    let outer = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let before_body = SourcePosition::new(Some(&outer), SourceOwner::Claim(proof), 2);
    assert_eq!(
        before_body
            .visible_fact(helper, &compiler.runtime)
            .unwrap_err()
            .route,
        "FactId/Producer"
    );
    let after_body = SourcePosition {
        before: 3,
        ..before_body
    };
    assert!(after_body.visible_fact(helper, &compiler.runtime).is_ok());
    let sealed = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(sealed.visible_fact(helper, &compiler.runtime).is_err());
    assert!(sealed
        .visible_fact(proof.stored.primary_fact_id(), &compiler.runtime)
        .is_ok());
}

#[test]
fn claim_rejects_missing_actual_parameter_introduction() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .introduced_params
        .defined_params
        .store_and_infer_results
        .clear();
    assert!(compiler
        .compile_run(&result, "missing_claim_parameter")
        .is_err());
}

#[test]
fn claim_rejects_missing_actual_domain_assumption() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .assumed_dom_facts
        .clear();
    let error = compiler
        .compile_run(&result, "missing_claim_domain")
        .expect_err("domain capture required");
    assert_eq!(error.route, "Forall/Domain");
}

#[test]
fn claim_rejects_missing_conclusion_and_mismatched_source_step() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .conclusion_proofs
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_claim_conclusion")
            .unwrap_err()
            .route,
        "Claim/Stages"
    );
    let (mut result, compiler) = checked(PLAIN);
    claim_mut(&mut result.statement_results[0])
        .statement
        .proof
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_claim_source_step")
            .unwrap_err()
            .route,
        "Claim/Stages"
    );
}

#[test]
fn claim_rejects_original_goal_that_differs_from_parent_store() {
    let (mut result, compiler) =
        checked("claim:\n    ? 1 = 1\n    1 = 1\nclaim:\n    ? 2 = 2\n    2 = 2\n");
    let other = claim(&result.statement_results[1]).statement.fact.clone();
    claim_mut(&mut result.statement_results[0]).statement.fact = other;
    assert!(compiler.compile_run(&result, "claim_other_goal").is_err());
}

#[test]
fn sketch_checks_its_body_without_a_claim_conclusion() {
    let (result, compiler) = checked("sketch:\n    1 = 1\n");
    let lean = compiler.compile_run(&result, "sketch_boundary").unwrap();
    assert!(lean.contains("private theorem _sketch_1"));
    assert!(!lean.lines().any(|line| line.starts_with("theorem h_")));
}
