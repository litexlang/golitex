use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::ExecStmtResult;
use crate::execute::execute_fact_stmt::{
    EqualityClassSearchMode, StrategySearch, VerifyFactResult, VerifyState,
};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn builtin_premises_cannot_reenter_until_the_intermediate_fact_is_stored() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have x R");
    exec_ok(&mut rt, "trust x >= 1");
    let before = memory_sizes(&rt);
    assert!(verify(&mut rt, "0 < (x + x) + (x + x)", builtin_only()).is_failed());
    assert_eq!(
        memory_sizes(&rt),
        before,
        "failed route must not store WD or truth"
    );
    assert!(!verify(&mut rt, "0 < x", builtin_only()).is_failed());
    assert!(
        !verify(&mut rt, "0 < x + x", builtin_only()).is_failed(),
        "direct known-bound citation remains available"
    );
    exec_ok(&mut rt, "0 < x");
    let before = memory_sizes(&rt);
    assert!(!verify(&mut rt, "0 < x + x", builtin_only()).is_failed());
    assert_eq!(
        memory_sizes(&rt),
        before,
        "premise lookup must remain read-only"
    );
    exec_ok(&mut rt, "0 < x + x");
    assert!(!verify(&mut rt, "0 < (x + x) + (x + x)", builtin_only()).is_failed());
}

#[test]
fn builtin_premises_keep_checked_application_and_calculation_leaves() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn bump(x Z) Z = x + 1");
    exec_ok(&mut rt, "have fn wrapped_bump(x Z) Z = bump(x)");
    let application = fact(&mut rt, "bump(3) = 4");
    assert!(
        !rt.verify_builtin_rule_premise(&application, builtin_only())
            .unwrap()
            .is_failed()
    );
    let nested_application = fact(&mut rt, "wrapped_bump(3) = 4");
    assert!(
        rt.verify_builtin_rule_premise(&nested_application, builtin_only())
            .unwrap()
            .is_failed()
    );
    for code in [
        "sum(3, 3, fn(x Z) Z {x}) = 3",
        "sum(3, 3, fn(x Z) Z {x + 1}) = 4",
        "reduce(2, 2, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2",
    ] {
        assert!(
            !verify(
                &mut rt,
                code,
                VerifyState::top_level().without_well_defined_storage()
            )
            .is_failed(),
            "{code}"
        );
    }
    assert!(verify(&mut rt, "sum(3, 3, fn(x Z) Z {x + 1}) = 5", builtin_only()).is_failed());
}

#[test]
fn deep_budget_does_not_disable_builtin_entry_or_reenable_a_disabled_entry() {
    let mut rt = runtime();
    let mut state = builtin_only();
    state.remaining_deep_search_depth = 0;
    assert!(!verify(&mut rt, "1 + 1 = 2", state.clone()).is_failed());
    state.can_use_builtin_rule = false;
    state.remaining_deep_search_depth = VerifyState::TOP_DEEP_SEARCH_DEPTH;
    assert!(verify(&mut rt, "1 + 1 = 2", state.after_deep_search()).is_failed());
    assert!(verify(&mut rt, "1 < 2", state).is_failed());
}

#[test]
fn stored_facts_and_zero_depth_strategy_calculation_remain_available() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have x R");
    exec_ok(&mut rt, "trust x >= 1");
    assert!(
        !verify(
            &mut rt,
            "x >= 1",
            VerifyState::top_level().known_only_no_wd()
        )
        .is_failed()
    );
    for code in ["1 + 1 = 2", "1 < 2"] {
        let goal = fact(&mut rt, code);
        assert!(
            !rt.verify_fact_in_strategy(&goal, StrategySearch { depth: 0 })
                .unwrap()
                .is_failed(),
            "{code}"
        );
    }
    let goal = fact(&mut rt, "0 < x + x");
    assert!(
        rt.verify_fact_in_strategy(&goal, StrategySearch { depth: 0 })
            .unwrap()
            .is_failed()
    );
}

#[test]
fn three_definition_layers_keep_their_independent_depth_boundary() {
    let mut rt = runtime();
    for code in [
        "prop positive_bound(x R):\n    x >= 1",
        "prop wrapped_bound(x R):\n    $positive_bound(x)",
        "prop twice_wrapped_bound(x R):\n    $wrapped_bound(x)",
        "have x R",
        "trust x >= 1",
    ] {
        exec_ok(&mut rt, code);
    }
    let state = VerifyState::top_level().without_well_defined_storage();
    assert!(!verify(&mut rt, "$twice_wrapped_bound(x)", state.clone()).is_failed());
    let mut shallow = state.clone();
    shallow.remaining_deep_search_depth = 2;
    assert!(verify(&mut rt, "$twice_wrapped_bound(x)", shallow).is_failed());
    assert!(
        !verify(&mut rt, "$twice_wrapped_bound(x)", state).is_failed(),
        "failed shallow search must not affect the later full search"
    );
}

#[test]
fn missing_strict_positivity_and_invalid_wd_still_fail() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have x R");
    exec_ok(&mut rt, "trust x >= 0");
    assert!(verify(&mut rt, "0 < x", builtin_only()).is_failed());
    assert!(verify(&mut rt, "0 < x + x", builtin_only()).is_failed());
    assert!(verify(&mut rt, "1 / 0 = 1 / 0", VerifyState::top_level()).is_failed());
}

#[test]
fn premise_policy_is_shared_by_greater_and_equality_rules() {
    let mut rt = runtime();
    for code in ["have x R", "have y R", "trust x > y"] {
        exec_ok(&mut rt, code);
    }
    assert!(!verify(&mut rt, "x + 1 > y + 1", builtin_only()).is_failed());
    assert!(
        verify(
            &mut rt,
            "((x + 1) + 1) + 1 > ((y + 1) + 1) + 1",
            builtin_only()
        )
        .is_failed()
    );
    exec_ok(&mut rt, "x + 1 > y + 1");
    assert!(!verify(&mut rt, "(x + 1) + 1 > (y + 1) + 1", builtin_only()).is_failed());
    assert!(!verify(&mut rt, "abs(x) * abs(y) = abs(x * y)", builtin_only()).is_failed());
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
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

fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let Stmt::Fact(fact) = parse(rt, code) else {
        panic!("fact: {code}")
    };
    fact
}

fn verify(rt: &mut Runtime, code: &str, state: VerifyState) -> VerifyFactResult {
    let goal = fact(rt, code);
    rt.verify_fact(&goal, state).unwrap()
}

fn builtin_only() -> VerifyState {
    let mut state = VerifyState::top_level().without_well_defined_storage();
    state.can_use_def_and_known_forall_and_known_strategy = false;
    state.can_use_rewrite = false;
    state.equality_class_search = EqualityClassSearchMode::StoredPathsOnly;
    state
}

fn memory_sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}
