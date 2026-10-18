use super::*;

fn checked(source: &str) -> (RunLitexCodeResult, Runtime) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(
        result.success && result.session_error.is_none(),
        "{}",
        crate::json_output::emit_run_detailed(&result, &runtime, "cursor", None)
    );
    (result, runtime)
}

fn witness(statement: &ExecStmtResult) -> &ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(proof),
    )) = statement
    else {
        panic!("witness")
    };
    proof
}

#[test]
fn geo_scope_cursor_witness_preserves_original_ids_and_blocks_future_and_closed_locals() {
    let (run, runtime) = checked("witness exist m, n R st {m = 0, n = 1} from 0, 1:\n    have hidden R\n    hidden + 1 = hidden + 1\n");
    let statement = &run.statement_results[0];
    let proof = witness(statement);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let caller = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(statement),
        witness_ambient_len(&proof.ambient, &[]),
    );
    assert_eq!(
        caller
            .visible_fact(proof.store_and_infer_result.primary_fact_id(), &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureReturn"
    );
    let full = SourcePosition::new(Some(&caller), SourceOwner::WitnessExist(proof), usize::MAX);
    let pending = SourcePosition::new(Some(&full), SourceOwner::WitnessExist(proof), 0);
    let member = proof
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let equality = proof.witness_equalities[0].primary_fact_id();
    assert_eq!(
        pending.visible_fact(member, &runtime).unwrap_err().route,
        "Scope/FutureProducer"
    );
    let parameter = &proof
        .statement
        .exist_shaped_fact_in_witness
        .plain()
        .typed_parameters
        .groups[0]
        .params[0];
    assert_eq!(
        pending
            .visible_parameter(parameter.id, &runtime)
            .unwrap_err()
            .route,
        "Identifier/FutureProducer"
    );
    let introduced = SourcePosition { before: 2, ..full };
    assert_eq!(
        introduced
            .visible_parameter(parameter.id, &runtime)
            .unwrap()
            .2,
        member
    );
    assert_eq!(
        introduced
            .visible_fact(equality, &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureProducer"
    );
    let first_equality = SourcePosition { before: 3, ..full };
    assert_eq!(
        first_equality.visible_fact(equality, &runtime).unwrap().1,
        format!("h_{}", equality.value())
    );
    let hidden = ordinary_have(&proof.proof_steps[0]).unwrap();
    let hidden_parameter = &hidden.statement.param_def.groups[0].params[0];
    let hidden_id = hidden.store_and_infer_result.store_and_infer_results[0].primary_fact_id();
    assert!(full
        .visible_parameter(hidden_parameter.id, &runtime)
        .is_ok());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &proof.proof_steps[1] else {
        panic!("local calculation")
    };
    let Fact::AtomicFact(AtomicFact::EqualFact(equal)) =
        verified_subject(&fact.verify_result).unwrap()
    else {
        panic!("equality")
    };
    assert!(full
        .with_visible_wd(&equal.left, &mut |_, _| Ok(()))
        .unwrap()
        .is_some());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside.visible_fact(hidden_id, &runtime).is_err());
    assert!(outside
        .visible_parameter(hidden_parameter.id, &runtime)
        .is_err());
    assert!(outside
        .with_visible_wd(&equal.left, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(outside.context_parameters().is_empty());
    assert!(outside
        .visible_fact(proof.store_and_infer_result.primary_fact_id(), &runtime)
        .is_ok());
}

#[test]
fn geo_scope_cursor_exist_formation_guard_precedes_dependent_division_wd() {
    let (run, runtime) = checked("witness exist m R st {m != 0, 1 / m = 1 / m} from 1\n");
    let proof = witness(&run.statement_results[0]);
    let FactWellDefinedProof::ExistFact(formation) = &proof.ambient.exist_fact_well_defined else {
        panic!("exist formation")
    };
    let fact = proof.statement.exist_shaped_fact_in_witness.plain();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let full = SourcePosition::new(
        Some(&root),
        SourceOwner::ExistWD(fact, formation),
        usize::MAX,
    );
    let before_guard = SourcePosition::new(Some(&full), SourceOwner::ExistWD(fact, formation), 1);
    let guard = formation.assumed_body_facts[0]
        .store_and_infer
        .primary_fact_id();
    assert_eq!(
        before_guard
            .visible_fact(guard, &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureProducer"
    );
    let after_guard = SourcePosition { before: 2, ..full };
    assert_eq!(
        after_guard.visible_fact(guard, &runtime).unwrap().1,
        format!("h_{}", guard.value())
    );
    let FactWellDefinedProof::Equality(div) = &formation.assumed_body_facts[1].well_defined else {
        panic!("dependent equality")
    };
    assert!(after_guard
        .with_visible_wd(div.left.obj(), &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(full
        .with_visible_wd(div.left.obj(), &mut |_, _| Ok(()))
        .unwrap()
        .is_some());
    assert!(root.visible_fact(guard, &runtime).is_err());
}

#[test]
fn geo_scope_cursor_contra_and_cases_keep_assumptions_and_closing_stores_local() {
    let (run, runtime) = checked("by contra:\n    ? 1 = 1\n    impossible 1 = 1\nby cases:\n    ? 1 = 1\n    ? 2 = 2\n    case 0 = 0:\n        1 = 1\n    case 0 != 0:\n        impossible 0 = 0\n");
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(contra))) =
        &run.statement_results[0]
    else {
        panic!("contra")
    };
    let caller = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[0]),
        1,
    );
    let full = SourcePosition::new(Some(&caller), SourceOwner::Contra(contra), usize::MAX);
    let pending = SourcePosition { before: 1, ..full };
    let assumption = contra.negation_assumed.primary_fact_id();
    assert_eq!(
        pending
            .visible_fact(assumption, &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureProducer"
    );
    assert!(SourcePosition { before: 2, ..full }
        .visible_fact(assumption, &runtime)
        .is_ok());
    let after_contra = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(after_contra.visible_fact(assumption, &runtime).is_err());
    assert!(after_contra
        .visible_fact(contra.stored.primary_fact_id(), &runtime)
        .is_ok());

    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(cases))) =
        &run.statement_results[1]
    else {
        panic!("cases")
    };
    let caller = SourcePosition::new(
        Some(&after_contra),
        SourceOwner::Statement(&run.statement_results[1]),
        cases.then_facts_wd.len() + 1,
    );
    let branch = &cases.branches[0];
    let scope = SourcePosition::new(Some(&caller), SourceOwner::CasesBranch(branch), usize::MAX);
    let sibling = cases.branches[1].assumptions_stored.primary_fact_id();
    assert!(scope.visible_fact(sibling, &runtime).is_err());
    let ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } = &branch.closing else {
        panic!("normal closing")
    };
    let head = 2 + branch.proof_steps.len();
    let first_id = proved_then_facts[0].store_and_infer.primary_fact_id();
    let second_id = proved_then_facts[1].store_and_infer.primary_fact_id();
    let first_done = SourcePosition {
        before: head + 2,
        ..scope
    };
    assert!(
        first_done.visible_fact(first_id, &runtime).is_ok(),
        "completed local closing must precede caller return"
    );
    assert_eq!(
        first_done
            .visible_fact(second_id, &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureProducer"
    );
    let after_cases = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(after_cases
        .visible_fact(branch.assumptions_stored.primary_fact_id(), &runtime)
        .is_err());
    for store in &cases.stored {
        assert!(after_cases
            .visible_fact(store.primary_fact_id(), &runtime)
            .is_ok());
    }
}

#[test]
fn geo_scope_cursor_obtain_uses_original_store_subjects_without_external_parameters() {
    let (run, runtime) =
        checked("witness exist m R st {m = 0} from 0\nobtain x from exist m R st {m = 0}\n");
    let statement = &run.statement_results[1];
    let (parameters, stores) = obtain_parts(statement).unwrap();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let pending = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 1);
    assert!(pending
        .visible_parameter(parameters[0].id, &runtime)
        .is_err());
    let full_statement = SourcePosition {
        before: usize::MAX,
        ..pending
    };
    let repeated = SourcePosition::new(Some(&full_statement), SourceOwner::Statement(statement), 1);
    assert_eq!(
        repeated
            .visible_parameter(parameters[0].id, &runtime)
            .unwrap_err()
            .route,
        "Identifier/FutureProducer"
    );
    let introduced = SourcePosition {
        before: 2,
        ..pending
    };
    assert_eq!(
        introduced
            .visible_parameter(parameters[0].id, &runtime)
            .unwrap()
            .2,
        stores.store_and_infer_results[0].primary_fact_id()
    );
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(after.context_parameters().is_empty());
    assert!(after.visible_parameter(parameters[0].id, &runtime).is_ok());
    for store in &stores.store_and_infer_results {
        assert!(after
            .visible_fact(store.primary_fact_id(), &runtime)
            .is_ok());
    }
}

#[test]
fn geo_scope_cursor_cart_coordinate_stores_follow_original_inference_order() {
    let (run, runtime) = checked("have fn dot(u, v cart(R, R)) R = u(1) * v(1) + u(2) * v(2)\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(statement),
    )) = &run.statement_results[0]
    else {
        panic!("formula function")
    };
    let VerifyObjWellDefinedResult::Success(formation) = &statement.anonymous_fn_well_defined
    else {
        panic!("function formation")
    };
    let (_, carriers, parameters, _, env) = function_binder(formation).unwrap();
    let store = &parameters.store_and_infer_results[0];
    let Some(InferResult::AtomicFact(infer)) = &store.infer else {
        panic!("membership inference")
    };
    let captured = atomic_inference_stages(infer);
    assert_eq!(captured.len(), 2);
    let seed = &env.facts.facts_by_id[&store.primary_fact_id()];
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let header = SourcePosition::new(Some(&root), SourceOwner::WD(formation), carriers.len() + 2);
    let first = captured[0].primary_fact_id();
    let second = captured[1].primary_fact_id();
    assert!(header.visible_fact(first, &runtime).is_ok());
    let pending = SourcePosition::new(Some(&header), SourceOwner::AtomicInference(seed, infer), 0);
    assert_eq!(
        pending.visible_fact(first, &runtime).unwrap_err().route,
        "Inference/FutureProducer"
    );
    let published = SourcePosition {
        before: 1,
        ..pending
    };
    assert!(published.visible_fact(first, &runtime).is_ok());
    assert_eq!(
        published.visible_fact(second, &runtime).unwrap_err().route,
        "Inference/FutureProducer"
    );
}

#[test]
fn geo_scope_cursor_set_constructor_children_respect_original_wd_prefix() {
    for source in [
        "let Interval = closed_range(1 + 0, 2 + 0)\n",
        "let Joined = union({1 + 0}, {2 + 0})\n",
        "let Families = power_set({3 + 0})\n",
    ] {
        let (run, _) = checked(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(statement)),
        )) = &run.statement_results[0]
        else {
            panic!("let constructor")
        };
        let VerifyObjWellDefinedResult::Success(formation) = &statement.value_well_defined else {
            panic!("constructor formation")
        };
        let (children, _) = arithmetic_stages(formation).expect("original child WD stages");
        assert!(!children.is_empty());
        let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        let full = SourcePosition::new(Some(&root), SourceOwner::WD(formation), usize::MAX);
        let pending = SourcePosition::new(Some(&full), SourceOwner::WD(formation), 0);
        assert!(pending
            .with_visible_wd(children[0].obj(), &mut |_, _| Ok(()))
            .unwrap()
            .is_none());
        let first_done = SourcePosition { before: 1, ..full };
        assert!(first_done
            .with_visible_wd(children[0].obj(), &mut |_, _| Ok(()))
            .unwrap()
            .is_some());
    }
}

#[test]
fn geo_scope_cursor_closed_scope_does_not_export_a_local_object_beside_a_numeric_leaf() {
    let (run, _) = checked("witness exist m R+ st {m = 1} from 1\n");
    let proof = witness(&run.statement_results[0]);
    let name = &proof
        .statement
        .exist_shaped_fact_in_witness
        .plain()
        .typed_parameters
        .groups[0]
        .params[0];
    let object = Obj::Identifier(IdentifierObj::from_bound_name(name));
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let local = SourcePosition::new(Some(&root), SourceOwner::WitnessExist(proof), usize::MAX);
    assert!(local
        .with_visible_inferred_subject(&object, &mut |_, _| Ok(()))
        .unwrap()
        .is_some());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside
        .with_visible_inferred_subject(&object, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
}

#[test]
fn geo_scope_cursor_atomic_success_views_share_exact_search_stage_boundaries() {
    let (run, _) = checked("tuple(7) $in cart(Z)\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[0]
    else {
        panic!("membership statement")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &statement.verify_result else {
        panic!("atomic result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        panic!("successful atomic result")
    };
    let stages = atomic_search_stages(proof);
    let AtomicSearchStage::WD(target) = stages[1] else {
        panic!("target domain WD")
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let full = SourcePosition::new(
        Some(&root),
        SourceOwner::Verify(&statement.verify_result),
        usize::MAX,
    );
    let direct = SourcePosition::new(Some(&full), SourceOwner::AtomicVerify(proof), usize::MAX);
    let pending = direct.atomic_search_prior(1).unwrap();
    assert!(visit_visible(
        &pending,
        &mut |evidence, _| {
            match evidence {
                SourceConstructor::Checked(candidate) if std::ptr::eq(candidate, target) => {
                    Ok(Some(()))
                }
                _ => Ok(None),
            }
        },
        &mut |_, _| Ok(None)
    )
    .unwrap()
    .is_none());
    let complete = direct.atomic_search_prior(2).unwrap();
    let mut exact = false;
    visit_visible(
        &complete,
        &mut |evidence, site| {
            if let SourceConstructor::Checked(candidate) = evidence {
                if std::ptr::eq(candidate, target) {
                    // Replay the actual completed constructor through the
                    // callback's pre-stage cursor. Its own completed children
                    // remain visible despite the inherited completion marker.
                    let (_, children, _, _, _) =
                        function_binder(target).expect("target function-domain formation");
                    let child = children[0].as_ref();
                    let replay = SourcePosition::new(Some(site), SourceOwner::WD(target), 1);
                    let nested = visit_visible(
                        &replay,
                        &mut |nested, _| match nested {
                            SourceConstructor::Checked(candidate)
                                if std::ptr::eq(candidate, child) =>
                            {
                                Ok(Some(()))
                            }
                            _ => Ok(None),
                        },
                        &mut |_, _| Ok(None),
                    )?;
                    assert!(
                        nested.is_some(),
                        "callback replay must retain the original completed child WD"
                    );
                    exact = true;
                    return Ok(Some(()));
                }
            }
            Ok(None)
        },
        &mut |_, _| Ok(None),
    )
    .unwrap();
    assert!(
        exact,
        "the exact original target WD is visible after its stage"
    );
    assert!(same_source_owner(direct.owner, full.owner));
}

fn declared_literal(statement: &ExecStmtResult) -> (&ExecHaveFnEqualStmtSuccessResult, Obj) {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(proof),
    )) = statement
    else {
        panic!("formula declaration");
    };
    (
        proof,
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(
            proof.statement.equal_to_anonymous_fn.clone(),
        )),
    )
}

#[test]
fn geo_scope_cursor_named_literal_reuse_requires_both_original_formation_stages() {
    let (run, runtime) = checked("have fn shifted(z R) R = z + 1\n");
    let statement = &run.statement_results[0];
    let (proof, literal) = declared_literal(statement);
    let complete = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    for before in [0, 1] {
        let pending =
            SourcePosition::new(Some(&complete), SourceOwner::Statement(statement), before);
        assert!(pending
            .with_visible_alias(&literal, &mut |_, _, _, _| Ok(()))
            .unwrap()
            .is_none());
    }
    let emitted = SourcePosition::new(Some(&complete), SourceOwner::Statement(statement), 2);
    let found = emitted
        .with_visible_alias(&literal, &mut |name, object, wd, producer| {
            assert_eq!(name, &proof.statement.name);
            assert_eq!(object, &literal);
            assert!(std::ptr::eq(wd, &proof.anonymous_fn_well_defined));
            assert_eq!(producer.before, 0);
            assert!(producer
                .with_visible_alias(&literal, &mut |_, _, _, _| Ok(()))
                .unwrap()
                .is_none());
            Ok(())
        })
        .unwrap();
    assert!(found.is_some());
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
    let reference = compiler
        .compile_object_reference(&literal, &emitted)
        .unwrap();
    assert!(reference.contains(&format!("_object_i{}", proof.statement.name.id.value())));
    assert!(!reference.contains("Litex.formulaFn"));
}

#[test]
fn geo_scope_cursor_named_literal_reuse_rejects_future_and_distinct_binder_identities() {
    let (run, _) = checked("have fn first(z R) R = z + 1\nhave fn second(w R) R = w + 1\n");
    let (_, later) = declared_literal(&run.statement_results[1]);
    let full = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let prefix = SourcePosition::new(Some(&full), SourceOwner::Run(&run), 1);
    assert!(prefix
        .with_visible_alias(&later, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(full
        .with_visible_alias(&later, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_some());
}

#[test]
fn geo_scope_cursor_named_literal_reuse_does_not_export_closed_claim_constructor() {
    let (run, _) = checked("claim:\n    ? 1 = 1\n    have fn hidden(w R) R = w + 1\n    1 = 1\n");
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &run.statement_results[0]
    else {
        panic!("claim");
    };
    let (steps, head) = claim_steps(claim);
    let (_, literal) = declared_literal(&steps[0]);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let local = SourcePosition::new(Some(&root), SourceOwner::Claim(claim), head + 1);
    assert!(local
        .with_visible_alias(&literal, &mut |_, _, _, position| Ok(position.is_local()))
        .unwrap()
        .unwrap());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside
        .with_visible_alias(&literal, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_none());
}
