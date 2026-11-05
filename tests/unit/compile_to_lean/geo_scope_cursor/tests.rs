use super::*;

#[test]
fn exp_log_constructor_reuse_checks_each_fresh_wd_before_aliasing() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ExpLogOperatorObjWellDefinedProofByDef as E;
    for expression in ["exp(a)", "ln(a)", "log(2,a)", "sqrt(a)"] {
        let (template, _) = checked(&format!("have a R+\n$is_set({expression})\n"));
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            template.statement_results.last().unwrap()
        else {
            panic!("sethood fact");
        };
        let object =
            super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                &statement.verify_result,
                0,
            )
            .unwrap()
            .unwrap()
            .obj()
            .clone();
        let (run, mut runtime) = checked("have a R+\n");
        // Ask the existing verifier for independent, uncommitted occurrences
        // in the same prefix. Result types deliberately do not implement Clone.
        let mut check = || {
            let VerifyObjWellDefinedResult::Success(wd) = runtime
                .verify_obj_well_definedness(
                    &object,
                    crate::execute::execute_fact_stmt::VerifyState::top_level(),
                )
                .unwrap()
            else {
                panic!("fresh WD");
            };
            assert!(matches!(
                wd.detailed_ref(),
                DetailedObjWellDefinedProof::ByDef { .. }
            ));
            wd
        };
        let original = check();
        let fresh = check();
        let changes = (0..3).map(|_| check()).collect::<Vec<_>>();
        let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
        let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
        let local = SourcePosition::new(Some(&root), SourceOwner::ObjectLocal(&original), 0);
        assert!(same_wd_constructor(&original, &fresh), "{expression}");
        assert_eq!(
            compiler.compile_wd(&fresh, &local).unwrap(),
            local.object_local_name(),
            "{expression}"
        );

        for (mutation, mut changed) in changes.into_iter().enumerate() {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::ExpLogOperator(proof),
                ..
            } = changed.as_detailed_mut().unwrap()
            else {
                panic!("exp/log constructor");
            };
            let (children, requirements) = match proof {
                E::Exp(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                E::Ln(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                E::Log(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                E::Sqrt(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
            };
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
                _ => {
                    let VerifyFactResult::AtomicExceptEquality(result) = &mut requirements[0]
                    else {
                        panic!("domain membership");
                    };
                    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_mut()
                    else {
                        panic!("checked membership");
                    };
                    let AtomicFact::InFact(fact) = &mut result.fact else {
                        panic!("membership");
                    };
                    fact.set = Obj::StandardSet(StandardSet::C);
                }
            }
            assert!(
                compiler.compile_wd(&changed, &local).is_err(),
                "{expression}, mutation {mutation}"
            );
        }
    }
}

#[test]
fn wd_subject_filter_retains_alpha_captures_calls_and_negative_keys() {
    let (run, _) = checked(
        "have a R\nhave b R\n\
         $is_set(fn(x R) R {a+x})\n\
         $is_set(fn(y R) R {a+y})\n\
         $is_set(fn(z R) R {b+z})\n\
         $is_set(fn(t R) R)\n\
         $is_set(fn(u R) R {a+u}(1))\n\
         $is_set(-3)\n",
    );
    let objects = run.statement_results[2..]
        .iter()
        .map(|statement| {
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
                panic!("sethood fact");
            };
            super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                &p.verify_result,
                0,
            )
            .unwrap()
            .unwrap()
            .obj()
        })
        .collect::<Vec<_>>();
    assert!(same_wd_subject(objects[0], objects[1]));
    assert!(same_wd_subject(objects[1], objects[0]));
    // Bound names may change; a different free capture must remain distinct.
    assert!(!same_wd_subject(objects[0], objects[2]));
    assert!(!same_wd_subject(objects[2], objects[0]));
    for other in [objects[3], objects[4]] {
        assert!(!same_wd_subject(objects[0], other));
        assert!(!same_wd_subject(other, objects[0]));
    }
    assert!(matches!(
        objects[3],
        Obj::FunctionSpace(FunctionSpace::FnSet(_))
    ));
    assert!(matches!(objects[4], Obj::FnObj(_)));
    let generated_negative = Obj::Literal(Literal::Number(Number::new("-3".into())));
    assert!(matches!(
        objects[5],
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(_))
    ));
    assert!(same_wd_subject(objects[5], &generated_negative));
    assert!(same_wd_subject(&generated_negative, objects[5]));
}

#[test]
fn wd_subject_filter_keeps_all_standard_set_keywords_distinct() {
    let sets = [
        StandardSet::NPos,
        StandardSet::N,
        StandardSet::Q,
        StandardSet::Z,
        StandardSet::R,
        StandardSet::C,
        StandardSet::QPos,
        StandardSet::RPos,
        StandardSet::QNeg,
        StandardSet::ZNeg,
        StandardSet::RNeg,
        StandardSet::QStar,
        StandardSet::ZStar,
        StandardSet::RStar,
        StandardSet::CStar,
    ]
    .map(Obj::StandardSet);
    for (i, left) in sets.iter().enumerate() {
        for (j, right) in sets.iter().enumerate() {
            assert_eq!(left.ir() == right.ir(), i == j);
            assert_eq!(same_wd_subject(left, right), i == j);
        }
        let number = Obj::Literal(Literal::Number(Number::new("1".into())));
        assert!(!same_wd_subject(left, &number));
        assert!(!same_wd_subject(&number, left));
    }
}

fn checked(source: &str) -> (RunLitexCodeResult, Runtime) {
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
fn geo_scope_cursor_completed_call_retains_original_argument_objects() {
    for (source, fields) in [
        (
            "have fn f(x R) R = x\n$is_set(f(1 + 2))\n",
            vec!["argument"],
        ),
        (
            "have fn f(x R, y R) R = x + y\n$is_set(f(1 + 2, 3 + 4))\n",
            vec!["first", "second"],
        ),
        (
            "have fn f(x cart(R, R)) cart(R, R) = x\n$is_set(f((1 + 2, 3 + 4)))\n",
            vec!["argument"],
        ),
        (
            "have fn f(x, y cart(R, R)) cart(R, R) = x\n$is_set(f((1, 2), (3, 4)))\n",
            vec!["argument.val.first", "argument.val.second"],
        ),
        (
            "$is_set(fn(x R: x != 0) R {x}(1 + 2))\n",
            vec!["function", "argument"],
        ),
    ] {
        let (run, _) = checked(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            run.statement_results.last().unwrap()
        else {
            panic!("completed function call")
        };
        let proof =
            super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                &statement.verify_result,
                0,
            )
            .unwrap()
            .unwrap();
        let (children, _) = arithmetic_stages(proof).unwrap();
        assert_eq!(children.len(), fields.len());
        let pending = SourcePosition::new(
            None,
            SourceOwner::Run(&run),
            run.statement_results.len() - 1,
        );
        let completed = SourcePosition::new(
            Some(&pending),
            SourceOwner::FormedSubjects(
                &statement.verify_result,
                &statement.store_and_infer_result,
            ),
            0,
        );
        for (child, field) in children.iter().zip(fields) {
            assert!(pending.bound_wd_child(child).is_none());
            let reference = completed
                .bound_wd_child(child)
                .expect("original call stores its argument");
            assert!(
                reference.ends_with(&format!(".val.{field}")),
                "{source}: {reference}"
            );
        }
    }
}

#[test]
fn geo_scope_cursor_call_projection_does_not_invent_erased_tuple_hosts() {
    for source in [
        "have fn f(x, y, z cart(R, R)) cart(R, R) = x\n$is_set(f((1, 2), (3, 4), (5, 6)))\n",
        "$is_set((1 + 2, 3 + 4))\n",
    ] {
        let (run, _) = checked(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            run.statement_results.last().unwrap()
        else {
            panic!("completed packed object")
        };
        let proof =
            super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
                &statement.verify_result,
                0,
            )
            .unwrap()
            .unwrap();
        let completed = SourcePosition::new(
            None,
            SourceOwner::FormedSubjects(
                &statement.verify_result,
                &statement.store_and_infer_result,
            ),
            0,
        );
        for child in arithmetic_stages(proof).unwrap().0 {
            assert!(completed.bound_wd_child(child).is_none(), "{source}");
        }
    }
}

#[test]
fn geo_scope_cursor_completed_wd_replay_retains_constructor_but_not_later_facts() {
    let (run, runtime) = checked("$is_set(1 + 2)\n3 = 3\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(first)) = &run.statement_results[0] else {
        panic!("original constructor")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(later)) = &run.statement_results[1] else {
        panic!("later fact")
    };
    let proof =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &first.verify_result,
            0,
        )
        .unwrap()
        .unwrap();
    let active = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let found = active
        .with_visible_wd(proof.obj(), &mut |original, producer| {
            assert!(std::ptr::eq(original, proof));
            // Reusing a completed object does not widen the fact prefix of its
            // original construction proof, even though the caller sees both facts.
            assert!(producer
                .visible_fact(first.store_and_infer_result.primary_fact_id(), &runtime)
                .is_err());
            assert!(producer
                .visible_fact(later.store_and_infer_result.primary_fact_id(), &runtime)
                .is_err());
            Ok(producer.bound_wd_child(original))
        })
        .unwrap()
        .flatten();
    assert!(
        found.is_some(),
        "the original constructor was already emitted"
    );
    let pending = SourcePosition::new(Some(&active), SourceOwner::Run(&run), 0);
    assert!(pending
        .with_visible_wd(proof.obj(), &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
}

#[test]
fn geo_scope_cursor_completed_forall_constructor_keeps_its_fact_prefix() {
    let (run, runtime) = checked("forall a R:\n    $is_set(a + 1)\n    $is_set(a + 2)\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[0]
    else {
        panic!("forall statement")
    };
    let VerifyFactResult::ForallFact(result) = &statement.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        result.as_ref()
    else {
        panic!("local introduction")
    };
    let first = &proof.proved_then_facts[0];
    let wd = super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
        &first.verify_result,
        0,
    )
    .unwrap()
    .unwrap();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let head = parameter_count(&proof.fact.typed_parameters.groups) + proof.assumed_dom_facts.len();
    let active = SourcePosition::new(Some(&root), SourceOwner::Forall(proof), head + 2);
    let found = active
        .with_visible_wd(wd.obj(), &mut |original, producer| {
            assert!(producer
                .visible_fact(first.store_and_infer.primary_fact_id(), &runtime)
                .is_err());
            assert!(producer
                .visible_fact(
                    proof.proved_then_facts[1].store_and_infer.primary_fact_id(),
                    &runtime
                )
                .is_err());
            Ok(producer.bound_wd_child(original))
        })
        .unwrap()
        .flatten();
    assert!(found.is_some());
    let pending = SourcePosition::new(Some(&active), SourceOwner::Forall(proof), head);
    assert!(pending
        .with_visible_wd(wd.obj(), &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
}

#[test]
fn geo_scope_cursor_projects_only_original_completed_wd_requirements() {
    let source = "$is_set((1 + 2) / 3)\n";
    let (run, _) = checked(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[0]
    else {
        panic!("atomic formation")
    };
    let proof =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &statement.verify_result,
            0,
        )
        .unwrap()
        .unwrap();
    let (children, requirements) = arithmetic_stages(proof).unwrap();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let formed = SourcePosition::new(
        Some(&root),
        SourceOwner::FormedSubjects(&statement.verify_result, &statement.store_and_infer_result),
        0,
    );
    for (requirement, suffix) in requirements.iter().zip([".wd.2.2", ".wd.1", ".wd.2.1"]) {
        assert!(formed
            .bound_wd_requirement(requirement)
            .unwrap()
            .ends_with(suffix));
        assert!(root.bound_wd_requirement(requirement).is_none());
    }
    let (_, child_requirements) = arithmetic_stages(&children[0]).unwrap();
    assert!(formed
        .bound_wd_requirement(&child_requirements[0])
        .unwrap()
        .contains(".val.left).wd.1"));

    let pending = SourcePosition::new(Some(&root), SourceOwner::WDLocals(proof, 0), 0);
    let completed = SourcePosition::new(Some(&root), SourceOwner::WDLocals(proof, 1), 1);
    assert!(pending
        .bound_wd_requirement(&child_requirements[0])
        .is_none());
    assert!(completed
        .bound_wd_requirement(&child_requirements[0])
        .is_some());
    // Emitting one child cannot publish the enclosing division's proofs.
    assert!(completed.bound_wd_requirement(&requirements[0]).is_none());

    let (other, _) = checked(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(other)) = &other.statement_results[0]
    else {
        panic!("independent equal source")
    };
    let other =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &other.verify_result,
            0,
        )
        .unwrap()
        .unwrap();
    for requirement in arithmetic_stages(other).unwrap().1 {
        assert!(
            formed.bound_wd_requirement(requirement).is_none(),
            "equal subjects and IDs from another result do not identify the emitted proof"
        );
    }
}

#[test]
fn geo_scope_cursor_local_blocks_reuse_only_completed_wd_registrations() {
    for source in [
        "witness exist m R st {m = 0} from 0:\n    $is_set(m + 1)\n    $is_set(m + 1)\n",
        "by contra:\n    ? 1 = 1\n    $is_set(1 + 1)\n    $is_set(1 + 1)\n    impossible 1 = 1\n",
        "by cases:\n    ? 1 = 1\n    case 0 = 0:\n        $is_set(1 + 1)\n        $is_set(1 + 1)\n    case 0 != 0:\n        impossible 0 = 0\n",
    ] {
        let (run, _) = checked(source);
        let statement = &run.statement_results[0];
        let owner = match statement {
            ExecStmtResult::Witness(_) => SourceOwner::WitnessExist(witness(statement)),
            ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
                SourceOwner::Contra(p)
            }
            ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(p))) => {
                SourceOwner::CasesBranch(&p.branches[0])
            }
            _ => panic!("local proof block"),
        };
        let (steps, head) = local_steps(owner).unwrap();
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(first)) = &steps[0] else {
            panic!("first formation")
        };
        let captured = &first.store_and_infer_result.formed_subjects[0];
        let object = super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &first.verify_result, captured.argument_index,
        ).unwrap().unwrap().obj();
        let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        let before = SourcePosition::new(Some(&root), owner, head);
        let after = SourcePosition { before: head + 1, ..before };
        assert_eq!(
            after.registered_wd_reference(object, Some(captured.wd_id)).unwrap(),
            Some(format!("_object_w{}", captured.wd_id.value())),
            "{source}"
        );
        assert!(before.registered_wd_reference(object, Some(captured.wd_id)).unwrap().is_none());
        let pending = SourcePosition::new(Some(&after), owner, head);
        assert!(pending.registered_wd_reference(object, None).unwrap().is_none());
        let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        assert!(outside.registered_wd_reference(object, None).unwrap().is_none());
    }
}

#[test]
fn geo_scope_cursor_local_chain_publishes_edges_before_nested_inference() {
    let (run, runtime) =
        checked("witness exist m R st {m = 0} from 0:\n    1 = 1 + 0 = 1\n    2 = 2\n");
    let proof = witness(&run.statement_results[0]);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(chain)) = &proof.proof_steps[0] else {
        panic!("chain statement")
    };
    let store = &chain.store_and_infer_result;
    let StoreFactResult::ChainFact(stored) = &store.store else {
        panic!("stored chain")
    };
    let Some(InferResult::ChainFact(inferred)) = &store.infer else {
        panic!("chain inference")
    };
    assert!(!inferred.transitive_closures.is_empty());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(later)) = &proof.proof_steps[1] else {
        panic!("later statement")
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let local = SourcePosition::new(Some(&root), SourceOwner::WitnessExist(proof), 2);
    let group = SourcePosition::new(Some(&local), SourceOwner::CompoundInference(store), 0);
    for edge in &stored.adjacent {
        assert_eq!(
            local
                .visible_fact(edge.fact_id, &runtime)
                .unwrap_err()
                .route,
            "Scope/FutureProducer"
        );
        assert_eq!(
            group.visible_fact(edge.fact_id, &runtime).unwrap().1,
            format!("h_{}", edge.fact_id.value())
        );
    }
    for closure in &inferred.transitive_closures {
        assert_eq!(
            group
                .visible_fact(closure.derived.primary_fact_id(), &runtime)
                .unwrap_err()
                .route,
            "Inference/FutureProducer"
        );
    }
    assert_eq!(
        group
            .visible_fact(later.store_and_infer_result.primary_fact_id(), &runtime)
            .unwrap_err()
            .route,
        "Scope/FutureProducer"
    );
    assert!(SourcePosition::new(None, SourceOwner::Run(&run), 1)
        .visible_fact(stored.adjacent[0].fact_id, &runtime)
        .is_err());
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
    let guard = formation.detailed_ref().assumed_body_facts[0]
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
    let FactWellDefinedProof::Equality(div) =
        &formation.detailed_ref().assumed_body_facts[1].well_defined
    else {
        panic!("dependent equality")
    };
    assert!(after_guard
        .with_visible_wd(div.detailed_ref().left.obj(), &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(full
        .with_visible_wd(div.detailed_ref().left.obj(), &mut |_, _| Ok(()))
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
fn case_statement_publishes_completed_builder_inferences_before_its_return() {
    use crate::execute::execute_proof_block_stmt::{
        ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
    };
    let (run, runtime) = checked(
        r#"thm contextual_tuple_case_publication:
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


"#,
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        crate::execute::ExecDefThmStmtResult::Success(theorem),
    )) = &run.statement_results[0]
    else {
        panic!("named theorem")
    };
    let crate::execute::ExecDefThmBodyProof::Forall(body) = &theorem.body else {
        panic!("forall theorem body")
    };
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &body.proof_steps[0]
    else {
        panic!("claim body")
    };
    let ExecClaimBodyProof::NonForall(body) = &claim.body else {
        panic!("plain claim")
    };
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(cases))) =
        &body.proof_steps[0]
    else {
        panic!("case split")
    };
    let branch = &cases.branches[1];
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &branch.proof_steps[3]
    else {
        panic!("builder membership")
    };
    let store = &statement.store_and_infer_result;
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    // The fourth statement is still being compiled in the enclosing branch.
    let scope = SourcePosition::new(Some(&root), SourceOwner::CasesBranch(branch), 5);
    let stages = prop_inference_stages(store);
    let (index, base) = stages
        .iter()
        .enumerate()
        .find(|(_, stage)| {
            scope
                .source_fact(stage.primary_fact_id(), &runtime)
                .is_ok_and(|fact| fact.ir().ends_with("$in cart(N+, N+)"))
        })
        .expect("original inferred base membership");
    let id = base.primary_fact_id();
    let pending = SourcePosition::new(Some(&scope), SourceOwner::PropInference(store), index);
    assert_eq!(
        pending.visible_fact(id, &runtime).unwrap_err().route,
        "Inference/FutureProducer"
    );
    let published = SourcePosition {
        before: index + 1,
        ..pending
    };
    assert!(published.visible_fact(id, &runtime).is_ok());
    assert_eq!(
        scope.visible_fact(id, &runtime).unwrap_err().route,
        "Scope/FutureProducer"
    );
    let sibling = SourcePosition::new(
        Some(&root),
        SourceOwner::CasesBranch(&cases.branches[0]),
        usize::MAX,
    );
    assert!(sibling.visible_fact(id, &runtime).is_err());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside.visible_fact(id, &runtime).is_err());
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
fn inferred_standard_set_uses_only_its_active_conclusion_subject() {
    let (run, runtime) = checked("have fn dot(u, v cart(R, R)) R = u(1) * v(1) + u(2) * v(2)\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(statement),
    )) = &run.statement_results[0]
    else {
        panic!("formula function");
    };
    let VerifyObjWellDefinedResult::Success(formation) = &statement.anonymous_fn_well_defined
    else {
        panic!("function formation");
    };
    let (_, _, parameters, _, _) = function_binder(formation).unwrap();
    let Some(InferResult::AtomicFact(infer)) = &parameters.store_and_infer_results[0].infer else {
        panic!("coordinate inference");
    };
    let captured = atomic_inference_stages(infer);
    let store = &captured[0].store;
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
    let outside = SourcePosition::new(None, SourceOwner::Term, 0);
    let inside = SourcePosition::new(
        Some(&outside),
        SourceOwner::InferredStore(store),
        usize::MAX,
    );
    let real = Obj::StandardSet(StandardSet::R);

    // The original inference supplies R directly, even without a separate WD
    // record. Neither an absent subject nor a sibling/outside scope can do so.
    assert_eq!(
        compiler.compile_object_reference(&real, &inside).unwrap(),
        crate::compile_to_lean::helper::standard_term(&StandardSet::R).unwrap()
    );
    assert!(compiler
        .compile_object_reference(&Obj::StandardSet(StandardSet::Z), &inside)
        .is_err());
    assert!(compiler.compile_object_reference(&real, &outside).is_err());
    // Formation provenance does not publish the fact being constructed.
    assert!(inside
        .visible_fact(store.primary_fact_id(), &compiler.runtime)
        .is_err());
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
        target.obj(),
        true,
        &|evidence, _| matches!(evidence, SourceConstructor::Checked(candidate)
            if same_wd_subject(candidate.obj(), target.obj())),
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
        target.obj(),
        true,
        &|evidence, _| {
            matches!(evidence, SourceConstructor::Checked(candidate)
            if same_wd_subject(candidate.obj(), target.obj()))
        },
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
                        child.obj(),
                        true,
                        &|evidence, _| {
                            matches!(evidence, SourceConstructor::Checked(candidate)
                            if same_wd_subject(candidate.obj(), child.obj()))
                        },
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
            .with_visible_alias(&literal, &runtime, &mut |_, _, _, _| Ok(()))
            .unwrap()
            .is_none());
    }
    let emitted = SourcePosition::new(Some(&complete), SourceOwner::Statement(statement), 2);
    let found = emitted
        .with_visible_alias(&literal, &runtime, &mut |name, object, wd, producer| {
            assert_eq!(name, &proof.statement.name);
            assert_eq!(object, &literal);
            assert!(std::ptr::eq(wd, &proof.anonymous_fn_well_defined));
            assert_eq!(producer.before, 0);
            assert!(producer
                .with_visible_alias(&literal, &runtime, &mut |_, _, _, _| Ok(()))
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
    let (run, runtime) = checked("have fn first(z R) R = z + 1\nhave fn second(w R) R = w + 1\n");
    let (_, later) = declared_literal(&run.statement_results[1]);
    let full = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let prefix = SourcePosition::new(Some(&full), SourceOwner::Run(&run), 1);
    assert!(prefix
        .with_visible_alias(&later, &runtime, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(full
        .with_visible_alias(&later, &runtime, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_some());
}

#[test]
fn geo_scope_cursor_named_literal_reuse_does_not_export_closed_claim_constructor() {
    let (run, runtime) =
        checked("claim:\n    ? 1 = 1\n    have fn hidden(w R) R = w + 1\n    1 = 1\n");
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
        .with_visible_alias(&literal, &runtime, &mut |_, _, _, position| Ok(
            position.is_local()
        ))
        .unwrap()
        .unwrap());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside
        .with_visible_alias(&literal, &runtime, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_none());
}
