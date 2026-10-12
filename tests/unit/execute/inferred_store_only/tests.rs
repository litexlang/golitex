use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn run(rt: &mut Runtime, source: &str) -> RunLitexCodeResult {
    let result = rt.run_litex_code(source).expect("public source execution");
    assert!(result.success && result.session_error.is_none(), "{source}");
    result
}

fn stored(statement: &ExecStmtResult) -> &StoreFactAndInferResult {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => &proof.store_and_infer_result,
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) => {
            &proof.stored
        }
        _ => panic!("stored fact statement"),
    }
}

fn has_fact(rt: &Runtime, readable: &str) -> bool {
    rt.execution_environments_stack.iter().any(|env| {
        env.facts
            .facts_by_id
            .values()
            .any(|fact| fact.readable_string() == readable)
    })
}

#[test]
fn inferred_store_only_strict_liveness_tracer() {
    let mut rt = runtime();
    run(
        &mut rt,
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/infer/atomic/one_step_store_only.lit"
        )),
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn inferred_store_only_predicate_requires_an_explicit_next_seed() {
    let mut rt = runtime();
    run(
        &mut rt,
        "prop inner(x R):\n    x = x\nprop outer(x R):\n    $inner(x)\nhave value R\n",
    );
    let result = run(&mut rt, "by def $outer(value)\n");
    assert!(has_fact(&rt, "$inner(value)"));
    assert!(
        !has_fact(&rt, "value = value"),
        "outer does not infer inner's consequences"
    );
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &stored(&result.statement_results[0]).infer
    else {
        panic!("outer inference")
    };
    let expanded = rules
        .iter()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(proof) => Some(proof),
            _ => None,
        })
        .unwrap();
    assert_eq!(expanded.derived.len(), 1);
    assert_eq!(expanded.derived[0].stored_fact_ids().len(), 1);
    run(&mut rt, "$inner(value)\n");
    assert!(
        has_fact(&rt, "value = value"),
        "the explicit next seed runs its own infer"
    );
}

#[test]
fn inferred_store_only_builder_stores_one_growth_step() {
    let mut rt = runtime();
    let result = run(
        &mut rt,
        "forall S set, x R:\n    S = {y R: y + 1 $in S}\n    x $in S\n    =>:\n        x = x\n",
    );
    let VerifyFactResult::ForallFact(proof) = (match &result.statement_results[0] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => &proof.verify_result,
        _ => panic!("forall statement"),
    }) else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("local forall")
    };
    let facts: Vec<_> = proof
        .local_env
        .facts
        .facts_by_id
        .values()
        .map(|fact| fact.readable_string())
        .collect();
    assert!(facts.iter().any(|fact| fact == "x + 1 $in S"));
    assert!(!facts.iter().any(|fact| fact.contains("x + 1 + 1")));
}

#[test]
fn inferred_store_only_subset_rule_stores_its_quantified_conclusion() {
    let mut rt = runtime();
    let result = run(&mut rt, "N $subset R\n");
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &stored(&result.statement_results[0]).infer
    else {
        panic!("subset inference")
    };
    let projected = rules
        .iter()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::SubsetElementwiseMembership(proof) => {
                Some(&proof.derived)
            }
            _ => None,
        })
        .unwrap();
    let StoreFactResult::ForallFact(stored) = &projected.store else {
        panic!("the named subset rule stores its universal conclusion directly")
    };
    assert_eq!(stored.fact.typed_parameters.groups.len(), 1);
    assert_eq!(projected.stored_fact_ids().len(), 1);
}

#[test]
fn inferred_store_only_permissions_remain_disabled_in_children() {
    let state = VerifyState::top_level().without_inference();
    assert!(!state
        .capped_at(VerifyStateLevel::KnownSpecialProperty)
        .allows_inference());
    assert!(!state
        .for_premises(VerifyStateLevel::BuiltinRule)
        .unwrap()
        .allows_inference());
    assert!(!state.after_rewrite().unwrap().allows_inference());
}

#[test]
fn inferred_store_only_false_goals_discard_all_tentative_consequences() {
    let mut rt = runtime();
    run(
        &mut rt,
        "prop inner(x R):\n    x = x\nprop outer(x R):\n    $inner(x)\nhave value R\n",
    );
    let before: Vec<_> = rt
        .execution_environments_stack
        .iter()
        .map(|env| env.facts.facts_by_id.len())
        .collect();
    let result = rt
        .run_litex_code("forall:\n    $outer(value)\n    =>:\n        0 = 1\n")
        .unwrap();
    assert!(!result.success && result.session_error.is_none());
    assert_eq!(
        before,
        rt.execution_environments_stack
            .iter()
            .map(|env| env.facts.facts_by_id.len())
            .collect::<Vec<_>>()
    );
    assert!(!has_fact(&rt, "$inner(value)"));
    run(&mut rt, "value = value\n");
}

#[test]
fn inferred_store_only_invalid_formation_never_stores() {
    let mut rt = runtime();
    let result = rt.run_litex_code("0 / 0 = 0\n").unwrap();
    assert!(!result.success && result.session_error.is_none());
    assert!(rt.top_exec_env().facts.facts_by_id.is_empty());
}

#[test]
fn inferred_store_only_prime_rule_stores_its_named_conclusions_without_wd() {
    use crate::store_fact_and_infer::InferBuiltinDefinitionResult;
    let mut rt = runtime();
    let result = run(&mut rt, "$prime(5)\n");
    let seed = stored(&result.statement_results[0]);
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &seed.infer
    else {
        panic!("prime seed inference")
    };
    let prime = rules
        .iter()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::BuiltinDefinition(
                InferBuiltinDefinitionResult::Prime(proof),
            ) => Some(proof),
            _ => None,
        })
        .expect("the named prime rule");
    assert_eq!(prime.source_fact_id, seed.primary_fact_id());
    assert_eq!(prime.derived.len(), 2);
    let StoreFactResult::ForallFact(trial) = &prime.derived[1].store else {
        panic!("trial-divisor conclusion")
    };
    assert!(Fact::ForallFact(trial.fact.clone())
        .readable_string()
        .contains("5 %"));
    assert!(rt.fact_by_id_in_stack(trial.fact.fact_id).is_some());
    let count = rt.top_exec_env().facts.facts_by_id.len();
    let rejected = rt.run_litex_code("$prime(4)\n").unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
}

#[test]
fn inferred_store_only_general_subset_carrier_uses_known_inputs_and_rolls_back_a_miss() {
    let mut rt = runtime();
    run(
        &mut rt,
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/known_subset_general_carrier.lit"
        )),
    );
    let count = rt.top_exec_env().facts.facts_by_id.len();
    let rejected = rt
        .run_litex_code("forall X, Y set, K power_set(X), point Y:\n    point $in X\n")
        .unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
}
