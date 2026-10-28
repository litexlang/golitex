use litex::ast::fact::Fact;
use litex::ast::obj::{Add, ArithmeticOperator, Literal, Number, Obj};
use litex::ast::stmt::Stmt;
use litex::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ObjWellDefinedProof, VerifyObjWellDefinedResult,
};
use litex::execute::execute_fact_stmt::VerifyState;
use litex::json_output::project_stmt_normal;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::result_detail::OutputDetail;
use litex::runtime::{Runtime, RuntimeError};
use litex::tokenize::Tokenizer;

fn command() -> LaunchCommand {
    LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    }
}

fn number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.into(),
    }))
}

fn parsed_fact(runtime: &mut Runtime, source: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(source, runtime.current_file.clone())
        .unwrap();
    let mut statements = runtime.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    let Stmt::Fact(fact) = statements.remove(0) else {
        panic!("expected fact: {source}")
    };
    fact
}

#[test]
fn compound_wd_drops_success_trees_without_hiding_a_later_failure() {
    use litex::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactWellDefinedResult;
    use litex::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactWellDefinedResult;
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        let Fact::AndFact(and) = parsed_fact(&mut runtime, "1 < 2 and 2 < 3") else {
            panic!("and")
        };
        let VerifyAndFactWellDefinedResult::Success(proof) = runtime
            .verify_and_fact_well_definedness(&and, VerifyState::top_level())
            .unwrap()
        else {
            panic!("valid and WD")
        };
        assert_eq!(proof.detail(), mode);
        if mode == OutputDetail::Detailed {
            assert_eq!(proof.as_detailed().unwrap().components.len(), 2);
        }

        let Fact::ChainFact(chain) = parsed_fact(&mut runtime, "1 < 2 < 3") else {
            panic!("chain")
        };
        let VerifyChainFactWellDefinedResult::Success(proof) = runtime
            .verify_chain_fact_well_definedness(&chain, VerifyState::top_level())
            .unwrap()
        else {
            panic!("valid chain WD")
        };
        assert_eq!(proof.detail(), mode);
        if mode == OutputDetail::Detailed {
            assert_eq!(proof.as_detailed().unwrap().adjacent.len(), 2);
        }

        let Fact::AndFact(and) = parsed_fact(&mut runtime, "1 = 1 and 1 / 0 = 1") else {
            panic!("and")
        };
        let VerifyAndFactWellDefinedResult::Failed(failure) = runtime
            .verify_and_fact_well_definedness(&and, VerifyState::top_level())
            .unwrap()
        else {
            panic!("invalid second conjunct")
        };
        assert_eq!(failure.failed_index, 1);
        assert_eq!(
            failure.succeeded_components.len(),
            usize::from(mode == OutputDetail::Detailed)
        );

        let Fact::ChainFact(chain) = parsed_fact(&mut runtime, "1 = 1 = 1 / 0") else {
            panic!("chain")
        };
        let VerifyChainFactWellDefinedResult::Failed(failure) = runtime
            .verify_chain_fact_well_definedness(&chain, VerifyState::top_level())
            .unwrap()
        else {
            panic!("invalid second edge")
        };
        assert_eq!(failure.failed_index, 1);
        assert_eq!(
            failure.succeeded_adjacent.len(),
            usize::from(mode == OutputDetail::Detailed)
        );
        assert!(runtime.run_litex_code("1 + 1 = 2").unwrap().success);
    }
}

#[test]
fn every_fact_wd_family_preserves_mode_and_closes_its_binder_scope() {
    use litex::execute::execute_fact_stmt::well_defined_results::{
        FactWellDefinedProof, VerifyFactWellDefinedResult,
    };
    let sources = [
        "1 = 1",
        "1 $in R",
        "1 < 2 and 2 < 3",
        "1 < 2 < 3",
        "1 = 1 or 1 = 2",
        "exist x R st {x = x}",
        "exist! x R st {x = 1}",
        "not exist x R st {x = x}",
        "forall x R:\n    x = x",
        "forall x R:\n    x != 0\n    =>:\n        1 / x = 1 / x\n    <=>:\n        x = x",
        "not forall x R:\n    x != 0\n    =>:\n        1 / x != 1 / x",
    ];
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        for source in sources {
            let fact = parsed_fact(&mut runtime, source);
            let VerifyFactWellDefinedResult::Success(proof) = runtime
                .verify_fact_well_definedness(&fact, VerifyState::top_level())
                .unwrap()
            else {
                panic!("{mode:?}: {source}")
            };
            assert_eq!(proof.detail(), mode, "{source}");
            assert!(proof.require_detail(mode, "test parent").is_ok());
            let wrong = if mode == OutputDetail::Normal {
                OutputDetail::Detailed
            } else {
                OutputDetail::Normal
            };
            assert!(matches!(
                proof.require_detail(wrong, "test parent"),
                Err(RuntimeError::InternalBug(_))
            ));
            if mode != OutputDetail::Detailed {
                let no_tree = match proof {
                    FactWellDefinedProof::OrFact(proof) => proof.as_detailed().is_err(),
                    FactWellDefinedProof::ExistFact(proof) => proof.as_detailed().is_err(),
                    FactWellDefinedProof::ForallFact(proof) => proof.as_detailed().is_err(),
                    FactWellDefinedProof::ForallFactWithIff(proof) => proof.as_detailed().is_err(),
                    FactWellDefinedProof::NotForall(proof) => proof.as_detailed().is_err(),
                    _ => true,
                };
                assert!(no_tree);
            }
            assert_eq!(runtime.execution_environments_stack.len(), 1);
        }
        assert!(runtime.run_litex_code("have x R").unwrap().success);
        assert!(
            !runtime.run_litex_code("x != 0").unwrap().success,
            "local WD guard leaked"
        );
        assert!(
            !runtime.run_litex_code("1 / x = 1 / x").unwrap().success,
            "local WD guard leaked"
        );
        assert!(runtime.run_litex_code("x = x").unwrap().success);
    }
}

#[test]
fn quantified_wd_keeps_failed_guard_order_in_every_mode() {
    use litex::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult;
    use litex::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult;
    use litex::execute::execute_fact_stmt::well_defined_results::{
        FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
    };
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        for source in [
            "forall x R:\n    1 / x = 1 / x\n    x != 0\n    =>:\n        x = x\n    <=>:\n        x = x",
            "not forall x R:\n    1 / x = 1 / x\n    x != 0\n    =>:\n        x = x",
        ] {
            let fact = parsed_fact(&mut runtime, source);
            let VerifyFactWellDefinedResult::Failed(failure) = runtime.verify_fact_well_definedness(&fact, VerifyState::top_level()).unwrap() else { panic!("later guard authorized earlier expression: {source}") };
            let (index, prior_types, prior_dom) = match failure {
                FailToVerifyFactWellDefinedResult::ForallFactWithIff(FailToVerifyForallFactWithIffWellDefinedResult::DomFact { failed_index, param_type_well_defined, succeeded_dom, .. }) => (failed_index, param_type_well_defined.len(), succeeded_dom.len()),
                FailToVerifyFactWellDefinedResult::NotForall(FailToVerifyNotForallFactWellDefinedResult::DomFact { failed_index, param_type_well_defined, succeeded_dom, .. }) => (failed_index, param_type_well_defined.len(), succeeded_dom.len()),
                _ => panic!("actual first guard WD failure"),
            };
            assert_eq!(index, 0);
            assert_eq!(prior_dom, 0);
            assert_eq!(prior_types, usize::from(mode == OutputDetail::Detailed));
            assert_eq!(runtime.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn every_wd_failure_owns_its_original_goal_without_a_source_overlay() {
    use litex::execute::execute_fact_stmt::well_defined_results::VerifyFactWellDefinedResult;
    let sources = [
        "1 / 0 = 1",
        "1 / 0 $in R",
        "1 = 1 and 1 / 0 = 1",
        "1 = 1 = 1 / 0",
        "1 / 0 = 1 or 1 = 1",
        "exist x R st {1 / 0 = x}",
        "exist! x R st {1 / 0 = x}",
        "not exist x R st {1 / 0 = x}",
        "forall x 1 / 0:\n    x = x",
        "forall x R:\n    1 / 0 = x",
        "forall x R:\n    =>:\n        1 / 0 = x\n    <=>:\n        x = x",
        "not forall x R:\n    1 / 0 = x",
    ];
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        for source in sources {
            let fact = parsed_fact(&mut runtime, source);
            let expected = fact.readable_string();
            let VerifyFactWellDefinedResult::Failed(failure) = runtime
                .verify_fact_well_definedness(&fact, VerifyState::top_level())
                .unwrap()
            else {
                panic!("{mode:?}: invalid fact WD accepted: {source}")
            };
            assert_eq!(failure.fact().readable_string(), expected);
            let run = runtime.run_litex_code(source).unwrap();
            assert!(!run.success && run.session_error.is_none(), "{source}");
            let output = project_stmt_normal(&run.statement_results[0], &runtime);
            let statement = output
                .as_object()
                .unwrap()
                .get("statement")
                .unwrap()
                .as_str()
                .unwrap();
            assert_eq!(statement, expected, "{mode:?}: {source}");
            assert!(!output.stringify().contains("<well_defined_not_proven>"));
            assert_eq!(runtime.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn scalar_wd_constructs_the_requested_payload_without_a_success_tree() {
    let object = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(number("1")),
        right: Box::new(number("1")),
    }));
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        let result = runtime
            .verify_obj_well_definedness(&object, VerifyState::top_level())
            .unwrap();
        let VerifyObjWellDefinedResult::Success(proof) = result else {
            panic!("valid sum WD rejected")
        };
        assert_eq!(proof.detail(), mode);
        match proof {
            ObjWellDefinedProof::Compact(proof) => assert!(proof.computation.is_none()),
            ObjWellDefinedProof::Normal(proof) => assert!(proof.computation.is_none()),
            ObjWellDefinedProof::Detailed(proof) => assert_eq!(proof.obj(), &object),
        }
    }
}

#[test]
fn failure_then_recovery_preserves_the_live_context_in_every_mode() {
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        assert!(runtime.run_litex_code("have a R = 2").unwrap().success);
        for source in ["a = 3", "1 / 0 = 1 / 0"] {
            let failed = runtime.run_litex_code(source).unwrap();
            assert!(
                !failed.success && failed.session_error.is_none(),
                "{mode:?}: {source}"
            );
            let json = project_stmt_normal(&failed.statement_results[0], &runtime).stringify();
            assert!(!json.is_empty());
        }
        assert!(runtime.run_litex_code("a + 1 = 3").unwrap().success);
    }
}

#[test]
fn extracting_a_different_mode_is_an_internal_bug() {
    let mut runtime = Runtime::new_with_result_detail(command(), OutputDetail::Detailed);
    let VerifyObjWellDefinedResult::Success(proof) = runtime
        .verify_obj_well_definedness(&number("1"), VerifyState::top_level())
        .unwrap()
    else {
        panic!("number WD rejected")
    };
    assert!(matches!(
        proof.into_normal(),
        Err(RuntimeError::InternalBug(_))
    ));
}

#[test]
fn normal_is_default_and_lean_always_requests_detailed() {
    assert_eq!(
        Runtime::new(command()).result_detail(),
        OutputDetail::Normal
    );
    let command = LaunchCommand::CompileToLean {
        path: "example.lit".into(),
        strict: true,
        language: OutputLanguage::English,
    };
    assert_eq!(
        Runtime::new_with_result_detail(command, OutputDetail::Compact).result_detail(),
        OutputDetail::Detailed
    );
}

#[test]
fn reduced_wd_preserves_checked_function_and_template_computations() {
    let sources = [
        include_str!("../examples/proof_nodes/equal/by_object_definition/by_fn_application/finite_function_coordinate_call.lit"),
        include_str!("../examples/proof_nodes/equal/by_object_definition/by_template/have_fn_equal_application.lit"),
        include_str!("../examples/proof_nodes/equal/by_builtin_rule/composition_left_identity.lit"),
    ];
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        for source in sources {
            let mut runtime = Runtime::new_with_result_detail(command(), mode);
            let run = runtime.run_litex_code(source).unwrap();
            assert!(
                run.success && run.session_error.is_none(),
                "{mode:?}: {source}"
            );
        }
    }
}

#[test]
fn detailed_output_rejects_a_reduced_execution_instead_of_reconstructing_it() {
    let mut runtime = Runtime::new(command());
    let run = runtime.run_litex_code("1 + 1 = 2").unwrap();
    let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        litex::json_output::project_stmt_detailed(&run.statement_results[0], &runtime)
    }));
    assert!(failure.is_err());
}

#[test]
fn reduced_failures_keep_the_goal_and_nested_failed_statement() {
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        for source in ["1 / 0 = 1 / 0", "claim:\n    ? 1 = 1\n    1 = 2\n"] {
            let run = runtime.run_litex_code(source).unwrap();
            assert!(!run.success && run.session_error.is_none());
            let output = project_stmt_normal(&run.statement_results[0], &runtime).stringify();
            assert!(!output.contains("<well_defined_not_proven>"), "{output}");
            assert!(
                output.contains(if source.starts_with("claim") {
                    "1 = 2"
                } else {
                    "1 / 0"
                }),
                "{output}"
            );
        }
    }
}

#[test]
fn forall_application_constructs_only_its_requested_evidence_and_still_checks_guards() {
    use litex::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        assert!(
            runtime
                .run_litex_code(
                    "forall x R:\n    x > 0\n    =>:\n        x != 0\nhave a R = 1\na > 0\nhave b R"
                )
                .unwrap()
                .success
        );
        let Fact::AtomicFact(goal) = parsed_fact(&mut runtime, "a != 0") else {
            panic!("atomic")
        };
        let proof = runtime
            .search_atomic_fact_proof_by_known_forall_fact(&goal, VerifyState::top_level())
            .unwrap()
            .expect("actual forall route");
        assert_eq!(proof.detail(), mode);
        match proof {
            SearchProofByKnownForallFact::Compact(_) => {}
            SearchProofByKnownForallFact::Normal(proof) => {
                assert_eq!(proof.cite.fact_id, proof.cited_fact.fact_id);
                assert_eq!(proof.cited_fact.dom_facts.len(), 1);
            }
            SearchProofByKnownForallFact::Detailed(proof) => {
                assert_eq!(proof.forall_parameters_match_what_args.len(), 1);
                assert_eq!(proof.arg_match_proofs.len(), 2);
                assert!(proof
                    .arg_match_proofs
                    .iter()
                    .all(|child| child.detail() == mode));
                let requirements = proof.instantiation_requirements.as_detailed().unwrap();
                assert_eq!(requirements.param_type_requirements.len(), 1);
                assert_eq!(requirements.proof_of_dom_facts.len(), 1);
            }
        }
        let Fact::AtomicFact(missing_guard) = parsed_fact(&mut runtime, "b != 0") else {
            panic!("atomic")
        };
        assert!(runtime
            .search_atomic_fact_proof_by_known_forall_fact(&missing_guard, VerifyState::top_level())
            .unwrap()
            .is_none());
        let Fact::AtomicFact(wrong_carrier) = parsed_fact(&mut runtime, "i != 0") else {
            panic!("atomic")
        };
        assert!(runtime
            .search_atomic_fact_proof_by_known_forall_fact(&wrong_carrier, VerifyState::top_level())
            .unwrap()
            .is_none());
        assert_eq!(runtime.execution_environments_stack.len(), 1);
        assert!(runtime.run_litex_code("1 + 1 = 2").unwrap().success);
    }
}

#[test]
fn normal_forall_citation_survives_the_scope_that_supplied_it() {
    use litex::execute::execute_fact_stmt::verify_atomic_fact::{
        AtomicExceptEqualityFactSearchedProof, SearchProofByKnownForallFact,
        VerifyAtomicExceptEqualityFactResult,
    };
    use litex::execute::execute_fact_stmt::verify_forall_fact::{
        VerifyForallFactProof, VerifyForallFactResult,
    };
    use litex::execute::execute_fact_stmt::VerifyFactResult;
    use litex::execute::{ExecFactStmtResult, ExecStmtResult};
    let mut runtime = Runtime::new_with_result_detail(command(), OutputDetail::Normal);
    assert!(
        runtime
            .run_litex_code("abstract_prop scope_p(x)")
            .unwrap()
            .success
    );
    let run = runtime.run_litex_code("forall a R:\n    forall x R:\n        x > 0\n        =>:\n            $scope_p(x)\n    a > 0\n    =>:\n        $scope_p(a)\n").unwrap();
    assert!(run.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &run.statement_results[0] else {
        panic!("statement")
    };
    let VerifyFactResult::ForallFact(result) = &stmt.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        result.as_ref()
    else {
        panic!("introduced forall")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &proof.proved_then_facts[0].verify_result
    else {
        panic!("then")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        panic!("then success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(
        SearchProofByKnownForallFact::Normal(application),
    ) = &proof.searched_proof
    else {
        panic!("known forall")
    };
    assert_eq!(application.cite.fact_id, application.cited_fact.fact_id);
    assert!(
        runtime.execution_environments_stack.iter().all(|env| !env
            .facts
            .facts_by_id
            .contains_key(&application.cite.fact_id)),
        "citation belongs to the closed local scope"
    );
    assert_eq!(application.cited_fact.dom_facts.len(), 1);
    assert_eq!(runtime.execution_environments_stack.len(), 1);
}

#[test]
fn known_strategy_uses_the_same_mode_boundary_as_forall_application() {
    use litex::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownStrategy;
    let source = include_str!("../examples/stmt_nodes/definition/def_strategy.lit");
    let (setup, _) = source.rsplit_once("$is_one(a)").unwrap();
    for mode in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), mode);
        assert!(runtime.run_litex_code(setup).unwrap().success);
        let Fact::AtomicFact(goal) = parsed_fact(&mut runtime, "$is_one(a)") else {
            panic!("atomic")
        };
        let proof = runtime
            .search_atomic_except_equality_fact_proof_by_known_strategy(
                &goal,
                VerifyState::top_level(),
            )
            .unwrap()
            .expect("selected strategy");
        assert_eq!(proof.detail(), mode);
        match proof {
            SearchProofByKnownStrategy::Compact(_) => {}
            SearchProofByKnownStrategy::Normal(proof) => {
                assert_eq!(proof.strategy_name, "use_is_one");
                assert_eq!(proof.then_index, 0);
                assert_eq!(proof.cited_fact.dom_facts.len(), 1);
            }
            SearchProofByKnownStrategy::Detailed(proof) => {
                assert_eq!(proof.strategy_name, "use_is_one");
                assert_eq!(proof.forall_parameters_match_what_args.len(), 1);
                assert_eq!(proof.arg_match_proofs.len(), 1);
                let requirements = proof.instantiation_requirements.as_detailed().unwrap();
                assert_eq!(requirements.param_type_requirements.len(), 1);
                assert_eq!(requirements.proof_of_dom_facts.len(), 1);
            }
        }
        assert!(runtime.run_litex_code("have b R").unwrap().success);
        let Fact::AtomicFact(goal) = parsed_fact(&mut runtime, "$is_one(b)") else {
            panic!("atomic")
        };
        assert!(runtime
            .search_atomic_except_equality_fact_proof_by_known_strategy(
                &goal,
                VerifyState::top_level()
            )
            .unwrap()
            .is_none());
        assert_eq!(runtime.execution_environments_stack.len(), 1);
        assert!(runtime.run_litex_code("1 + 1 = 2").unwrap().success);
    }
}

#[test]
fn normal_whole_compound_forall_reports_the_actual_cited_rule() {
    for (source, goal) in [
        ("forall t R:\n    t=t and t=t\nhave a R=2\n", "a=2 and 2=a"),
        ("forall t R:\n    t=t=t\nhave a R=2\n", "a=a=a"),
    ] {
        let mut runtime = Runtime::new_with_result_detail(command(), OutputDetail::Normal);
        assert!(runtime.run_litex_code(source).unwrap().success);
        let run = runtime.run_litex_code(goal).unwrap();
        assert!(run.success);
        let normal = project_stmt_normal(&run.statement_results[0], &runtime);
        let method = normal
            .as_object()
            .unwrap()
            .get("proof_method")
            .unwrap()
            .as_object()
            .unwrap();
        assert!(
            method.get("cite").is_some(),
            "selected whole-forall citation: {normal:?}"
        );
        assert!(!normal.stringify().contains("arg_match_proofs"));
        assert!(!normal.stringify().contains("param_type_requirements"));
    }
}
