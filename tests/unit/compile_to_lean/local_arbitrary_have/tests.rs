use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualFactResult, InferResult};
use std::rc::Rc;

const CANCELLATION: &str =
    "thm local_witness_cancel:\n    ? forall x R:\n        x+0=x\n    have y R\n    (x+0)+y=x+y\n";
const DEPENDENT: &str = "thm dependent_local_values:\n    ? forall x R:\n        x+0=x\n    have y R\n    have shifted R=y+1\n    let second_shift=shifted+1\n    second_shift=shifted+1\n    (x+0)+second_shift=x+second_shift\n";
const SETS: &str = "thm local_sets:\n    ? 1=1\n    have A, B set\n    $is_set(A)\n    let alias=A\n    alias=A\n    have D set=A\n    D=A\n";

fn theorem(statement: &ExecStmtResult) -> &ExecDefThmStmtSuccess {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) => proof,
        _ => panic!("successful named theorem"),
    }
}

fn steps(proof: &ExecDefThmStmtSuccess) -> &[ExecStmtResult] {
    match &proof.body {
        ExecDefThmBodyProof::Forall(body) => &body.proof_steps,
        ExecDefThmBodyProof::NonForall(body) => &body.proof_steps,
    }
}

fn steps_mut(proof: &mut ExecDefThmStmtSuccess) -> &mut Vec<ExecStmtResult> {
    match &mut proof.body {
        ExecDefThmBodyProof::Forall(body) => &mut body.proof_steps,
        ExecDefThmBodyProof::NonForall(body) => &mut body.proof_steps,
    }
}

fn local_have(statement: &ExecStmtResult) -> &ExecHaveObjInNonemptySetStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) => proof,
        _ => panic!("ordinary local have"),
    }
}

fn local_have_mut(
    statement: &mut ExecStmtResult,
) -> &mut ExecHaveObjInNonemptySetStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) => proof,
        _ => panic!("ordinary local have"),
    }
}

fn public_signature(output: &str, id: FactId) -> &str {
    let start = output
        .find(&format!("theorem h_{}", id.value()))
        .expect("public original theorem");
    let declaration = &output[start..];
    &declaration[..declaration.find(" :=\n").expect("public proof delimiter")]
}

#[test]
fn local_arbitrary_have_uses_recorded_witness_member_and_cancellation_inside_original_goal() {
    let (result, compiler) = super::execute(CANCELLATION);
    let proof = theorem(&result.statement_results[0]);
    let local = local_have(&steps(proof)[0]);
    let parameter = &local.statement.param_def.groups[0].params[0];
    let member_id = local.groups[0].defined_params.store_and_infer_results[0].primary_fact_id();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &steps(proof)[1] else {
        panic!("the local member supplies the original cancellation seed")
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &seed.store_and_infer_result.infer
    else {
        panic!("recorded equality inference")
    };
    let [InferEqualFactResult::AdditiveCancellation(rule)] = rules.as_slice() else {
        panic!("the original residual equality is actually inferred")
    };
    let derived_id = rule.derived.store.primary_fact_id();
    let output = super::compile_run(&result, &compiler, "local_witness_cancel")
        .expect("local existence elimination");
    let id = parameter.id.value();
    assert!(output.contains(&format!("obtain ⟨_witness_i{id}, _member_i{id}⟩")));
    assert!(output.contains(&format!(
        "semanticObject (M := M) _witness_i{id} (M.member_isSet _member_i{id})"
    )));
    assert!(output.contains(&format!(
        "have h_{} : Litex.In _value_i{id}",
        member_id.value()
    )));
    assert!(output.contains("Litex.addCancelRightRight"));
    assert!(
        output
            .rsplit_once("exact ")
            .expect("final source conclusion")
            .1
            .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
            .any(|name| name == format!("h_{}", derived_id.value())),
        "the final proof must cite the actual cancellation producer"
    );
    let signature = public_signature(&output, proof.statement.fact.fact_id());
    for forbidden in [
        format!("_value_i{id}"),
        format!("_Host_i{id}"),
        format!("h_{}", member_id.value()),
        format!("_witness_i{id}"),
    ] {
        assert!(
            !signature.contains(&forbidden),
            "local witness escapes through {forbidden}: {signature}"
        );
    }
    let Fact::ForallFact(goal) = &proof.statement.fact else {
        panic!("original forall")
    };
    let external = goal.typed_parameters.groups[0].params[0].id.value();
    assert!(signature.contains(&format!("_Host_i{external} : Type v{external}")));
    assert!(signature.contains(&format!("Litex.Representation M _Host_i{external}")));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn local_arbitrary_have_keeps_all_numeric_carriers_internal_and_publishes_actual_ids() {
    let source = "thm local_numeric_members:\n    ? 1=1\n    have n N, z Z, q Q, r R, c C\n    n $in C\n    z $in C\n    q $in C\n    r $in C\n    c $in C\n";
    let (result, compiler) = super::execute(source);
    let proof = theorem(&result.statement_results[0]);
    let local = local_have(&steps(proof)[0]);
    let output = super::compile_run(&result, &compiler, "all_local_carriers")
        .expect("all five existing nonempty carriers");
    assert_eq!(output.matches("obtain ⟨_witness_i").count(), 5);
    let signature = public_signature(&output, proof.statement.fact.fact_id());
    assert!(!signature.contains("_value_i") && !signature.contains("Litex.In"));
    for store in &local.store_and_infer_result.store_and_infer_results {
        for id in store.stored_fact_ids() {
            assert!(
                output.contains(&format!("have h_{}", id.value())),
                "missing actual local producer"
            );
            assert!(!signature.contains(&format!("h_{}", id.value())));
        }
    }
}

#[test]
fn local_arbitrary_have_preserves_dependent_typed_have_and_let_without_public_witnesses() {
    let (result, compiler) = super::execute(DEPENDENT);
    let proof = theorem(&result.statement_results[0]);
    let local = local_have(&steps(proof)[0]);
    let id = local.statement.param_def.groups[0].params[0].id.value();
    let output = super::compile_run(&result, &compiler, "dependent_local_values")
        .expect("local typed RHS and let depend on the actual witness");
    assert!(output.contains(&format!("let _value_i{id} := Litex.semanticObject")));
    assert!(output.matches("let _object_i").count() >= 2);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(alias)),
    )) = &steps(proof)[2]
    else {
        panic!("original dependent let")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(alias_use)) = &steps(proof)[3] else {
        panic!("original alias equation")
    };
    let VerifyFactResult::Equality(alias_use) = &alias_use.verify_result else {
        panic!("alias equality verification")
    };
    let VerifyEqualityResult::Success(alias_use) = alias_use.as_ref() else {
        panic!("successful alias equality")
    };
    assert!(matches!(
        alias_use.searched_proof,
        EqualFactSearchedProof::ByEquivalenceClass(_)
    ));
    let alias_name = format!("h_{}", alias.stored_fact_ids[0].value());
    assert!(
        output
            .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
            .filter(|name| *name == alias_name)
            .count()
            >= 2,
        "the actual let equality producer is retained and consumed"
    );
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(calculation)) = &steps(proof)[4] else {
        panic!("recorded dependent calculation")
    };
    let VerifyFactResult::Equality(calculation) = &calculation.verify_result else {
        panic!("calculation equality")
    };
    let VerifyEqualityResult::Success(calculation) = calculation.as_ref() else {
        panic!("successful calculation")
    };
    assert!(matches!(calculation.searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation::Rational {}
        ))));
    let signature = public_signature(&output, proof.statement.fact.fact_id());
    assert!(!signature.contains(&format!("_value_i{id}")));
    assert!(!signature.contains("_object_i") && !signature.contains("_witness_i"));
    assert!(!output.contains("noncomputable def _object_i"));
}

#[test]
fn local_arbitrary_have_set_kind_uses_only_recorded_sethood_and_internal_aliases() {
    let (result, compiler) = super::execute(SETS);
    let proof = theorem(&result.statement_results[0]);
    let local = local_have(&steps(proof)[0]);
    let output = super::compile_run(&result, &compiler, "local_set_kind")
        .expect("set-kind has no nonempty obligation");
    assert_eq!(
        output
            .matches("M.standard_isSet Litex.StandardSetValue.complex")
            .count(),
        2
    );
    assert!(!output.contains("obtain ⟨_witness") && !output.contains("Litex.IsNonempty"));
    assert!(!public_signature(&output, proof.statement.fact.fact_id()).contains("_value_i"));
    for store in &local.store_and_infer_result.store_and_infer_results {
        assert!(output.contains(&format!(
            "have h_{} : Litex.IsSet",
            store.primary_fact_id().value()
        )));
        assert!(
            store
                .infer
                .as_ref()
                .expect("seed inference")
                .stored_fact_ids()
                .is_empty(),
            "set-kind publishes no fabricated equality"
        );
    }
}

#[test]
fn local_arbitrary_have_rejects_missing_nonempty_or_member_capture_and_wrong_subjects() {
    for change in [
        "nonempty",
        "carrier",
        "members",
        "member_subject",
        "goal_header",
    ] {
        let (mut result, compiler) = super::execute(CANCELLATION);
        let proof = super::named_theorem_mut(&mut result.statement_results[0]);
        if change == "goal_header" {
            let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
                &mut proof.goal_wd
            else {
                panic!("original goal WD")
            };
            goal.as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear();
            goal.as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .stored_fact_ids
                .clear();
        } else {
            let local = local_have_mut(&mut steps_mut(proof)[0]);
            match change {
                "nonempty" => local.groups[0].nonempty_check = ParamTypeFactCheckResult::Set,
                "carrier" => {
                    let ParamTypeFactCheckResult::Obj(proof) = &mut local.groups[0].nonempty_check
                    else {
                        panic!("numeric nonempty")
                    };
                    let AtomicFact::IsNonemptySetFact(fact) =
                        &mut super::atomic_proof_mut(proof).fact
                    else {
                        panic!("nonempty subject")
                    };
                    fact.set = Obj::StandardSet(StandardSet::Q);
                }
                "members" => {
                    local.groups[0]
                        .defined_params
                        .store_and_infer_results
                        .clear();
                    local.groups[0].defined_params.stored_fact_ids.clear();
                    local.store_and_infer_result.store_and_infer_results.clear();
                    local.store_and_infer_result.stored_fact_ids.clear();
                }
                "member_subject" => {
                    local.store_and_infer_result.store_and_infer_results.clear();
                    let stored =
                        Rc::get_mut(&mut local.groups[0].defined_params.store_and_infer_results[0])
                            .expect("group is the sole store owner after removing aggregate alias");
                    let StoreFactResult::AtomicFact(stored) = &mut stored.store else {
                        panic!("member store")
                    };
                    let AtomicFact::InFact(member) = &mut stored.fact else {
                        panic!("member")
                    };
                    member.element = super::number_object("7");
                    local
                        .store_and_infer_result
                        .store_and_infer_results
                        .push(Rc::clone(
                            &local.groups[0].defined_params.store_and_infer_results[0],
                        ));
                }
                _ => unreachable!(),
            }
        }
        super::compile_run(&result, &compiler, "missing_local_have_evidence")
            .expect_err("body or Runtime data cannot replace deleted/wrong original evidence");
    }
}

#[test]
fn local_arbitrary_have_source_step_cannot_be_deleted_or_replaced() {
    for change in ["deleted", "capture"] {
        let (mut result, compiler) = super::execute(CANCELLATION);
        let proof = super::named_theorem_mut(&mut result.statement_results[0]);
        if change == "deleted" {
            steps_mut(proof).remove(0);
        } else {
            local_have_mut(&mut steps_mut(proof)[0])
                .statement
                .param_def
                .groups[0]
                .param_type = ParamType::Obj(Obj::StandardSet(StandardSet::Q));
        }
        let error = super::compile_run(&result, &compiler, "deleted_original_local_step")
            .expect_err("an original source declaration must be replayed exactly");
        assert!(error.route == "Theorem/Stages" || error.route == "Theorem/ProofStepCapture");
    }
}

#[test]
fn local_arbitrary_have_prefix_visibility_rejects_future_parameter_and_later_same_group_member() {
    let source = "thm local_pair:\n    ? 1=1\n    have a, b R\n    a=a\n    b=b\n";
    let (result, compiler) = super::execute(source);
    let proof = theorem(&result.statement_results[0]);
    let local = local_have(&steps(proof)[0]);
    let first = &local.statement.param_def.groups[0].params[0];
    let second = &local.statement.param_def.groups[0].params[1];
    let pending = SourcePosition::new(None, SourceOwner::Named(proof), 0);
    let object = Obj::Identifier(IdentifierObj::from_bound_name(first));
    assert_eq!(
        compiler
            .compile_object_reference(&object, &pending)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
    let complete = SourcePosition {
        before: 1,
        ..pending
    };
    assert_eq!(
        compiler
            .compile_object_reference(&object, &complete)
            .unwrap(),
        format!("_value_i{}", first.id.value())
    );
    let current = SourcePosition::new(Some(&pending), SourceOwner::Statement(&steps(proof)[0]), 1);
    compiler
        .compile_object_reference(&object, &current)
        .expect("first witness is already introduced");
    let later = Obj::Identifier(IdentifierObj::from_bound_name(second));
    assert_eq!(
        compiler
            .compile_object_reference(&later, &current)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
}

#[test]
fn local_arbitrary_have_same_surface_names_keep_distinct_closed_scope_ids() {
    let source = format!(
        "{CANCELLATION}\n{}",
        CANCELLATION.replace("local_witness_cancel", "local_witness_again")
    );
    let (mut result, compiler) = super::execute(&source);
    let first = theorem(&result.statement_results[0]);
    let first_local = local_have(&steps(first)[0]);
    let first_id = first_local.statement.param_def.groups[0].params[0].id;
    let first_member =
        first_local.store_and_infer_result.store_and_infer_results[0].primary_fact_id();
    let second = theorem(&result.statement_results[1]);
    let second_id = local_have(&steps(second)[0]).statement.param_def.groups[0].params[0].id;
    assert_ne!(first_id, second_id);
    let output = super::compile_run(&result, &compiler, "distinct_closed_local_scopes")
        .expect("same spelling in distinct scopes has distinct identities");
    for id in [first_id, second_id] {
        assert!(output.contains(&format!(
            "let _value_i{} := Litex.semanticObject",
            id.value()
        )));
    }
    let proof = super::named_theorem_mut(&mut result.statement_results[1]);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &mut steps_mut(proof)[1] else {
        panic!("second cancellation seed")
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &mut seed.store_and_infer_result.infer
    else {
        panic!("equality inference")
    };
    let InferEqualFactResult::AdditiveCancellation(rule) = &mut rules[0] else {
        panic!("cancellation")
    };
    super::atomic_proof_mut(&mut rule.common_in_c_proof).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: first_member,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    let error = super::compile_run(&result, &compiler, "closed_member_citation")
        .expect_err("an earlier closed theorem's local member cannot supply the new witness");
    assert!(
        error.route == "FactId/Resolution" || error.route == "FactId/Producer",
        "{error}"
    );
}
