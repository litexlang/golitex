use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
};
use crate::execute::execute_fact_stmt::{StrategySearch, VerifyFactResult, VerifyState};
use crate::execute::ExecStmtResult;
use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn zero_fuel_definition_codomain_and_range_work_with_fresh_and_cached_wd() {
    for cached in [false, true] {
        for goal in ["id(a) $in R", "id(a) $in fn_range(id)"] {
            let mut rt = runtime();
            exec_ok(&mut rt, "have fn id(x R) R = x");
            exec_ok(&mut rt, "have a R = 1");
            if cached {
                exec_ok(&mut rt, "id(a) = id(a)");
            }
            let before = memory_sizes(&rt);
            let target = atomic(&mut rt, goal);
            let result = rt
                .verify_fact(&Fact::AtomicFact(target), zero_fuel())
                .unwrap();
            assert_special(result, goal);
            assert_eq!(
                before,
                memory_sizes(&rt),
                "known search must not store facts or WD"
            );
        }
    }
}

#[test]
fn cached_literal_application_uses_definition_without_reproving_the_domain() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "id(1) = id(1)");
    let target = atomic(&mut rt, "id(1) $in R");
    assert_special(
        rt.verify_fact(&Fact::AtomicFact(target), zero_fuel())
            .unwrap(),
        "cached literal",
    );
}

#[test]
fn stored_fact_wins_over_definition_property_in_both_entries() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R = 1");
    exec_ok(&mut rt, "id(a) $in R");
    for strategy in [false, true] {
        let target = Fact::AtomicFact(atomic(&mut rt, "id(a) $in R"));
        let result = if strategy {
            rt.verify_fact_in_strategy(&target, StrategySearch { depth: 0 })
                .unwrap()
        } else {
            rt.verify_fact(&target, zero_fuel()).unwrap()
        };
        let VerifyFactResult::AtomicExceptEquality(result) = result else {
            panic!("atomic")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
            panic!("known")
        };
        assert!(matches!(
            result.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
        ));
    }
}

#[test]
fn zero_strategy_depth_uses_the_same_known_special_property_phase() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R = 1");
    let target = Fact::AtomicFact(atomic(&mut rt, "id(a) $in R"));
    let result = rt
        .verify_fact_in_strategy(&target, StrategySearch { depth: 0 })
        .unwrap();
    assert_special(result, "strategy depth zero");
}

#[test]
fn invalid_domain_wrong_return_and_missing_definition_are_rejected() {
    for (setup, goal) in [
        ("have fn id(x N) N = x", "id(0 - 1) $in N"),
        ("have fn id(x R) R = a", "id(a) $in N"),
        ("have fn id(x R: x > 0) R = x", "id(0) $in R"),
        ("have f R", "f(1) $in R"),
    ] {
        let mut rt = runtime();
        exec_ok(&mut rt, "have a R");
        exec_ok(&mut rt, setup);
        let target = atomic(&mut rt, goal);
        assert!(
            rt.verify_fact(&Fact::AtomicFact(target), VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{goal}"
        );
    }
}

#[test]
fn exact_property_lookup_does_not_borrow_an_alias_row() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R = 1");
    exec_ok(&mut rt, "let alias = id");
    exec_ok(&mut rt, "alias(a) = alias(a)");
    let target = atomic(&mut rt, "alias(a) $in R");
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_special_property(&target)
        .is_none());
}

#[test]
fn property_return_match_can_cite_a_stored_set_equality() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R = 1");
    exec_ok(&mut rt, "let carrier = R");
    let target = atomic(&mut rt, "id(a) $in carrier");
    let before = memory_sizes(&rt);
    assert_special(
        rt.verify_fact(&Fact::AtomicFact(target), zero_fuel())
            .unwrap(),
        "stored return equality",
    );
    assert_eq!(before, memory_sizes(&rt));
}

#[test]
fn new_route_has_bilingual_normal_and_typed_detailed_output() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
        exec_ok(&mut rt, "have fn id(x R) R = x");
        exec_ok(&mut rt, "have a R = 1");
        let result = exec_ok(&mut rt, "id(a) $in R");
        let normal = project_stmt_normal(&result, &rt).stringify();
        let expected = if language == OutputLanguage::English {
            "known_special_property"
        } else {
            "已知特殊属性"
        };
        assert!(normal.contains(expected), "{normal}");
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        for marker in [
            "by_known_special_property",
            "FnApplicationInCodomain",
            "cite_definition_fact_id",
            "signature_matches",
        ] {
            assert!(detailed.contains(marker), "missing {marker}: {detailed}");
        }
    }
}

#[test]
fn fixed_builtin_premises_retain_definition_evidence_without_storing_the_premise() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn positive(x R) N+ = 1");
    exec_ok(&mut rt, "have a R");
    let before = memory_sizes(&rt);
    let target = atomic(&mut rt, "positive(a) >= 1");
    let mut state = zero_fuel();
    state.can_use_builtin_rule_round = 1;
    let result = rt.verify_fact(&Fact::AtomicFact(target), state).unwrap();
    assert!(!result.is_failed());
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(proof) = result.searched_proof else {
        panic!("builtin")
    };
    use super::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        greater_equal::GreaterEqualFactSearchProofByBuiltinRule,
        AtomicExceptEqualityFactSearchProofByBuiltinRule,
    };
    let AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
        GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(proof),
    ) = proof
    else {
        panic!("positive natural premise")
    };
    assert!(matches!(
        proof.premise_proof.searched_proof.as_ref(),
        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(_)
    ));
    assert_eq!(before, memory_sizes(&rt));
    let result = exec_ok(&mut rt, "positive(a) >= 1");
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(
        json.contains("premise_proof") && json.contains("by_known_special_property"),
        "{json}"
    );
}

#[test]
fn stored_equality_aligns_fixed_order_premises_without_entering_search() {
    let mut rt = runtime();
    for code in [
        "have a R = 2",
        "have b R = 2",
        "have c R = 1",
        "a > c",
        "a = b",
    ] {
        exec_ok(&mut rt, code);
    }
    let AtomicFact::GreaterFact(goal) = atomic(&mut rt, "b > c") else {
        panic!("greater")
    };
    let before = memory_sizes(&rt);
    let proof = rt.known_greater_proof(&goal.left, &goal.right).unwrap();
    assert!(proof.cite_fact_id().is_some());
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) = *proof.searched_proof
    else {
        panic!("stored")
    };
    assert!(matches!(proof.why_parameters_of_known_fact_are_equal_to_givens[0], crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof::ByEquivalenceClass(_)));
    assert_eq!(before, memory_sizes(&rt));
}

#[test]
fn cached_wd_from_an_equal_function_cannot_select_an_inapplicable_definition_signature() {
    // Deliberate assumption fixture: test signature selection under a stored
    // function equality, rather than asking the verifier to derive that equality.
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    for code in [
        "have f fn(x N) N",
        "have g fn(x R) R",
        "trust f = g",
        "have a R",
        "f(a) = f(a)",
    ] {
        exec_ok(&mut rt, code);
    }
    let target = atomic(&mut rt, "f(a) $in N");
    let before = memory_sizes(&rt);
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_special_property(&target)
        .is_none());
    assert_eq!(before, memory_sizes(&rt));
}

#[test]
fn scoped_definitions_expire_when_their_environment_is_popped() {
    let mut rt = runtime();
    rt.push_local_exec_env();
    exec_ok(&mut rt, "have fn local(x R) R = x");
    exec_ok(&mut rt, "have a R");
    let target = atomic(&mut rt, "local(a) $in R");
    assert_special(
        rt.verify_fact(&Fact::AtomicFact(target.clone()), zero_fuel())
            .unwrap(),
        "local property",
    );
    rt.pop_local_exec_env();
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_special_property(&target)
        .is_none());
}

#[test]
fn bounded_codomain_fallback_retains_its_selected_signature_citation() {
    let mut rt = runtime();
    for code in ["have fn id(x R) R = x", "let alias = id", "have a R"] {
        exec_ok(&mut rt, code);
    }
    let target = atomic(&mut rt, "alias(a) $in R");
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_special_property(&target)
        .is_none());
    let result = rt
        .verify_fact(
            &Fact::AtomicFact(target),
            VerifyState::top_level().without_well_defined_storage(),
        )
        .unwrap();
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("codomain")
    };
    use super::search_atomic_except_equality_fact_proof_by_builtin_strategy::AtomicExceptEqualityFactSearchProofByBuiltinStrategy;
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnApplicationInCodomain(proof),
    ) = result.searched_proof
    else {
        panic!("bounded strategy")
    };
    let signature = rt
        .fact_by_id_in_stack(proof.cite_signature_fact_id)
        .unwrap();
    assert!(signature.readable_string().contains("id $in fn"));
    assert!(!proof.proof_of_requirement_facts.is_empty());
    let stmt_result = exec_ok(&mut rt, "alias(a) $in R");
    let json = project_stmt_detailed(&stmt_result, &rt).stringify();
    assert!(json.contains("cite_signature_fact_id"), "{json}");
}

#[test]
fn read_only_known_lookup_does_not_call_order_duality_back_into_itself() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have a R");
    exec_ok(&mut rt, "have b R");
    let AtomicFact::GreaterFact(goal) = atomic(&mut rt, "a > b") else {
        panic!("greater")
    };
    let before = memory_sizes(&rt);
    assert!(rt.known_greater_proof(&goal.left, &goal.right).is_none());
    assert!(rt.known_less_proof(&goal.right, &goal.left).is_none());
    assert_eq!(before, memory_sizes(&rt));
}

#[test]
fn imported_function_definitions_keep_the_known_special_property_route() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/module_manager/known_special_property");
    let result = crate::run_module::run_project(LaunchCommand::Repository {
        path,
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(result.run.success, "{:?}", result.run.session_error);
    let main = result.files.last().unwrap();
    assert_eq!(main.run.statement_results.len(), 4);
    for result in &main.run.statement_results[2..] {
        let ExecStmtResult::Fact(
            crate::execute::execute_fact_stmt::result::ExecFactStmtResult::Success(result),
        ) = result
        else {
            panic!("fact")
        };
        let VerifyFactResult::AtomicExceptEquality(result) = &result.verify_result else {
            panic!("atomic")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_ref() else {
            panic!("success")
        };
        assert!(matches!(
            result.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(_)
        ));
    }
}

#[test]
fn equality_antisymmetry_retains_both_read_only_order_citations() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    for code in ["have a R", "have b R", "trust a <= b", "trust b <= a"] {
        exec_ok(&mut rt, code);
    }
    let target = Fact::AtomicFact(atomic(&mut rt, "a = b"));
    let before = memory_sizes(&rt);
    let mut state = zero_fuel();
    state.can_use_builtin_rule_round = 1;
    let VerifyFactResult::Equality(result) = rt.verify_fact(&target, state).unwrap() else {
        panic!("equality")
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{VerifyEqualityResult, EqualFactSearchedProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
    let VerifyEqualityResult::Success(result) = *result else {
        panic!("success")
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(proof),
    ) = result.searched_proof
    else {
        panic!("antisymmetry")
    };
    let left_id = proof.left_le_right_proof.cite_fact_id().unwrap();
    let right_id = proof.right_le_left_proof.cite_fact_id().unwrap();
    assert_ne!(left_id, right_id);
    assert_eq!(before, memory_sizes(&rt));
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn zero_fuel() -> VerifyState {
    VerifyState::top_level().known_only_no_wd()
}

fn parse(rt: &mut Runtime, code: &str) -> Stmt {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut stmts = rt.parse(&tokens).unwrap();
    assert_eq!(stmts.len(), 1);
    stmts.remove(0)
}

fn exec_ok(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let stmt = parse(rt, code);
    let result = rt.exec_stmt(&stmt).unwrap();
    assert!(!result.is_failed(), "{code}");
    result
}

fn atomic(rt: &mut Runtime, code: &str) -> AtomicFact {
    let Stmt::Fact(Fact::AtomicFact(fact)) = parse(rt, code) else {
        panic!("{code}")
    };
    fact
}

fn assert_special(result: VerifyFactResult, label: &str) {
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("{label}")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("{label}")
    };
    assert!(
        matches!(
            result.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(_)
        ),
        "{label}"
    );
}

fn memory_sizes(rt: &Runtime) -> Vec<(usize, usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.well_defined_objects.object_to_wd_id.len(),
                env.special_object_properties_by_def
                    .values()
                    .map(Vec::len)
                    .sum(),
            )
        })
        .collect()
}
