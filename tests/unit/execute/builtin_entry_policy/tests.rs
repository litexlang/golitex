use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn maintained_shared_level_tracer_uses_real_statement_transactions() {
    let result = runtime()
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/shared_search_levels.lit",
        )))
        .unwrap();
    assert!(result.success);
}

#[test]
fn direct_closed_calculation_tracer_restores_finite_enumeration() {
    let result = runtime()
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/direct_closed_calculation.lit",
        )))
        .unwrap();
    assert!(result.success);
}

#[test]
fn direct_result_distinguishes_calculation_citation_and_miss() {
    use crate::ast::fact::AtomicFact;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::closed_calculation_proof::{
        ClosedCalculationProof as C, ClosedValuePair,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::direct_atomic_fact_search_result::DirectAtomicFactSearchResult as D;
    let mut rt = runtime();
    let Fact::AtomicFact(goal) = fact(&mut rt, "1/3 + 1/3 = 2/3") else {
        panic!("atomic")
    };
    let AtomicFact::EqualFact(equal) = &goal else {
        panic!("equal")
    };
    assert!(rt
        .lookup_known_obj_equality(&equal.left, &equal.right)
        .is_none());
    let before = memory_sizes(&rt);
    let D::ByClosedCalculation(C::Equality(proof)) = rt.search_atomic_fact_proof_directly(&goal)
    else {
        panic!("calculation")
    };
    assert!(matches!(proof.values, ClosedValuePair::Rational { .. }));
    assert_eq!(memory_sizes(&rt), before);
    exec_ok(&mut rt, "1/3 + 1/3 = 2/3");
    assert!(matches!(
        rt.search_atomic_fact_proof_directly(&goal),
        D::ByKnownFact(_)
    ));
    let Fact::AtomicFact(wrong) = fact(&mut rt, "1/3 = 1/2") else {
        panic!("atomic")
    };
    assert!(matches!(
        rt.search_atomic_fact_proof_directly(&wrong),
        D::NotFound
    ));
    assert!(calculate_closed_atomic_fact(&wrong).is_none());

    let Fact::AtomicFact(member) = fact(&mut rt, "7/11 $in Q") else {
        panic!("atomic")
    };
    assert!(rt.lookup_known_atomic_fact(&member).is_none());
    assert!(matches!(
        rt.search_atomic_fact_proof_directly(&member),
        D::ByClosedCalculation(C::AtomicExceptEquality(_))
    ));
    exec_ok(&mut rt, "7/11 $in Q");
    assert!(matches!(
        rt.search_atomic_fact_proof_directly(&member),
        D::ByKnownFact(_)
    ));
}

#[test]
fn direct_calculation_covers_polarities_and_fails_closed() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    for code in [
        "1+1=2",
        "1/3+1/3=2/3",
        "1/3 != 1/2",
        "1/3<1/2",
        "1/2>1/3",
        "1/3<=1/3",
        "1/3>=1/3",
        "not 1/3>1/2",
        "not 1/2<1/3",
        "not 1/3>=1/2",
        "not 1/2<=1/3",
        "1/3 $in Q+",
        "not 1/3 $in Z",
        "(-1) $in Z-",
        "not 0 $in N+",
        "i*i = -1",
        "i != 0",
        "i $in C*",
        "not i $in R",
    ] {
        let Fact::AtomicFact(goal) = fact(&mut rt, code) else {
            panic!("atomic")
        };
        assert!(calculate_closed_atomic_fact(&goal).is_some(), "{code}");
    }
    for code in [
        "1+1=3",
        "1/3>1/2",
        "not 1/3<1/2",
        "1/3 $in Z",
        "not 1 $in R",
        "i < 1",
        "i = 0",
        "1/0=1/0",
        "1/0 $in R",
        "not 1/0 $in R",
        "p(3)=p(3)",
        "2^1000 = 3",
        "1/340282366920938463463374607431768211456 = 2/680564733841876926926749214863536422912",
    ] {
        let Fact::AtomicFact(goal) = fact(&mut rt, code) else {
            panic!("atomic")
        };
        assert!(calculate_closed_atomic_fact(&goal).is_none(), "{code}");
    }
    for code in ["1/0=1/0", "p(3)=p(3)", "1+1=3", "i<1"] {
        assert!(
            verify(&mut rt, code, VerifyState::new(VerifyStateLevel::Direct)).is_failed(),
            "{code}"
        );
        let stmt = parse(&mut rt, code);
        let before = memory_sizes(&rt);
        assert!(rt.exec_stmt(&stmt).unwrap().is_failed(), "{code}");
        assert_eq!(memory_sizes(&rt), before);
    }
}

#[test]
fn direct_never_uses_symbolic_normalization_definitions_or_known_value_substitution() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::direct_atomic_fact_search_result::DirectAtomicFactSearchResult as D;
    let mut rt = runtime();
    exec_ok(&mut rt, "have a R = 2");
    exec_ok(&mut rt, "have fn f(x R) R = x+1");
    for code in [
        "a+1=3",
        "a+0=a",
        "f(1)=2",
        "(a,a)=(2,2)",
        "finite_set_size({a})=1",
    ] {
        let Fact::AtomicFact(goal) = fact(&mut rt, code) else {
            panic!("atomic")
        };
        assert!(
            matches!(rt.search_atomic_fact_proof_directly(&goal), D::NotFound),
            "{code}"
        );
    }
    // SP constructor matching can now discharge its numeric equality at level 0.
    assert!(!verify(
        &mut rt,
        "f(1+1)=f(2)",
        VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
    )
    .is_failed());
}

#[test]
fn direct_json_retains_exact_evidence_and_no_fabricated_citation() {
    let mut rt = runtime();
    for (code, evidence) in [
        ("1/3+1/3=2/3", "rational"),
        ("1/3<1/2", "comparison"),
        ("1/3 $in Q", "exact_complex"),
    ] {
        let result = exec_ok(&mut rt, code);
        let detail = crate::json_output::project_stmt_detailed(&result, &rt);
        let searched = detail
            .as_object()
            .unwrap()
            .get("verify")
            .unwrap()
            .as_object()
            .unwrap()
            .get("searched_proof")
            .unwrap()
            .as_object()
            .unwrap();
        assert_eq!(
            searched.get("type").unwrap().as_str().unwrap(),
            "by_closed_calculation"
        );
        assert!(searched.get("cite_fact_id").is_none());
        let detailed = detail.stringify();
        assert!(detailed.contains("by_closed_calculation"), "{detailed}");
        assert!(detailed.contains(evidence), "{detailed}");
    }
}

#[test]
fn known_predicate_domain_is_reused_with_its_citation_at_level_zero() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have k N+ = 1");
    exec_ok(&mut rt, "k > 0");
    let before = memory_sizes(&rt);
    assert!(!verify(&mut rt, "k > 0", VerifyState::new(VerifyStateLevel::Direct)).is_failed());
    assert!(verify(&mut rt, "k < 0", VerifyState::new(VerifyStateLevel::Direct)).is_failed());
    assert_eq!(memory_sizes(&rt), before);
    let result = exec_ok(&mut rt, "k > 0");
    let json = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("by_known_fact_domain"), "{json}");
    assert!(json.contains("cite_fact_id"), "{json}");
}

#[test]
fn constructor_descent_keeps_a_fixed_leaf_ceiling() {
    let mut rt = runtime();
    for code in [
        "have a R",
        "have b R = a",
        "have fn f(x R) R = x",
        "have fn g(x R) R = x",
    ] {
        exec_ok(&mut rt, code);
    }
    let goal = fact(&mut rt, "f(g(a)) = f(g(b))");
    let Fact::AtomicFact(goal) = goal else {
        panic!("atomic")
    };
    assert!(rt
        .search_atomic_fact(
            &goal,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
        )
        .unwrap()
        .is_some());
    assert!(rt
        .search_atomic_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_none());
}

#[test]
fn shared_levels_have_one_premise_policy_and_consume_rewrite_once() {
    use VerifyStateLevel::*;
    let top = VerifyState::top_level();
    for (stage, ceiling) in [
        (KnownSpecialProperty, Direct),
        (BuiltinRule, KnownSpecialProperty),
        (Strategy, BuiltinRule),
        (DefinitionAndForall, BuiltinRule),
    ] {
        let child = top.for_premises(stage).unwrap();
        assert_eq!(child.level(), ceiling);
        assert!(child.after_rewrite().is_none());
        assert!(child.for_premises(stage).is_none());
    }
    let residual = top.after_rewrite().unwrap();
    assert_eq!(residual.level(), DefinitionAndForall);
    assert!(residual.after_rewrite().is_none());
    assert_eq!(VerifyState::new(Direct).capped_at(Strategy).level(), Direct);
}

#[test]
fn direct_cannot_reenter_property_and_raw_known_cannot_calculate() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R");
    for text in ["p = (p(1),p(2))", "id(a) $in R"] {
        let goal = fact(&mut rt, text);
        let Fact::AtomicFact(atomic) = goal else {
            panic!("atomic")
        };
        let before = memory_sizes(&rt);
        assert!(
            rt.search_atomic_fact(&atomic, VerifyState::new(Direct))
                .unwrap()
                .is_none(),
            "{text}"
        );
        assert!(
            rt.search_atomic_fact(&atomic, VerifyState::new(KnownSpecialProperty))
                .unwrap()
                .is_some(),
            "{text}"
        );
        assert_eq!(before, memory_sizes(&rt));
    }
    for text in ["1+1=2", "1<2"] {
        assert!(!verify(&mut rt, text, VerifyState::new(Direct)).is_failed());
        assert!(!verify(&mut rt, text, VerifyState::new(BuiltinRule)).is_failed());
    }
}

#[test]
fn stored_paths_remain_available_at_level_zero_and_keep_wd() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    exec_ok(&mut rt, "have a R = 1");
    exec_ok(&mut rt, "have b R = a");
    exec_ok(&mut rt, "have c R = b");
    exec_ok(&mut rt, "have p cart(R,R)");
    assert!(!verify(&mut rt, "c=1", VerifyState::new(Direct)).is_failed());
    for bad in ["1/0=1/0", "p(3)=p(3)", "1+1=3"] {
        assert!(
            verify(&mut rt, bad, VerifyState::top_level()).is_failed(),
            "{bad}"
        );
    }
}

#[test]
fn bounded_definition_body_normalization_keeps_strategy_premises_restricted() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn bump(x Z) Z = x+1");
    exec_ok(&mut rt, "have fn wrapped(x Z) Z = bump(x)");
    assert!(!verify(&mut rt, "bump(3)=4", VerifyState::top_level()).is_failed());
    let child = VerifyState::top_level().for_premises(Strategy).unwrap();
    let goal = fact(&mut rt, "bump(3)=4");
    assert!(rt
        .verify_strategy_requirements(vec![goal], child)
        .unwrap()
        .is_none());
    // Top-level definition evaluation now expands the two known bodies locally.
    // This does not grant definition search to a strategy's restricted child.
    assert!(verify(&mut rt, "wrapped(3)=4", child).is_failed());
    assert!(!verify(&mut rt, "wrapped(3)=4", VerifyState::top_level()).is_failed());
    exec_ok(&mut rt, "bump(3)=4");
    assert!(!verify(&mut rt, "wrapped(3)=4", VerifyState::top_level()).is_failed());
}

#[test]
fn exploratory_wd_does_not_record_but_fact_commit_records_checked_subjects() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn id(x R) R = x");
    exec_ok(&mut rt, "have a R");
    let before = memory_sizes(&rt);
    assert!(!verify(&mut rt, "id(a)=id(a)", VerifyState::top_level()).is_failed());
    assert_eq!(memory_sizes(&rt), before);
    exec_ok(&mut rt, "id(a)=id(a)");
    let after = memory_sizes(&rt);
    assert!(after.last().unwrap().1 > before.last().unwrap().1);
    let stable = memory_sizes(&rt);
    assert!(verify(&mut rt, "id(a)=id(1/0)", VerifyState::top_level()).is_failed());
    assert_eq!(memory_sizes(&rt), stable);
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

// Literal heads parse, but equality identity still requires valid domains.
#[test]
fn literal_object_heads_check_wd_while_retired_dimension_syntax_rejects_at_parse() {
    let run = runtime().run_litex_code("(1,2)(3)=(1,2)(3)").unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert_eq!(run.statement_results.len(), 1);
    assert!(run.statement_results[0].is_failed());
    let run = runtime().run_litex_code("tuple_dim((1,2))=2").unwrap();
    assert!(!run.success && run.session_error.is_some());
    assert!(run.statement_results.is_empty());
}
