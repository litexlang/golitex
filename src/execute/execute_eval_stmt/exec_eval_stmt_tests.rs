use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_eval_stmt::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult,
};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
    runtime
        .exec_stmt(&stmts[0])
        .expect("exec_stmt RuntimeResult")
}

fn assert_eval_number(runtime: &mut Runtime, code: &str, expected: &str) {
    let outcome = exec_one(runtime, code);
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
            success,
        ))) => match success.evaluated_object {
            Obj::Literal(Literal::Number(Number { normalized_value })) => {
                assert_eq!(normalized_value, expected);
            }
            other => panic!("expected number {expected}, got {other:?}"),
        },
        other => panic!(
            "expected eval Success for `{code}`, failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn eval_closed_pow_succeeds_with_nine() {
    let mut runtime = runtime_with_file_env();
    assert_eval_number(&mut runtime, "eval (1 + 2)^2", "9");
}

#[test]
fn normalized_decimal_and_guarded_imaginary_regressions() {
    for code in [
        "2.400 = 2.4",
        "2.000 $in Z",
        "i != 0",
        "0 != i",
        "1 / i = -i",
        "i / i = 1",
        "1/3 != 2/3",
    ] {
        assert!(
            !exec_one(&mut runtime_with_file_env(), code).is_failed(),
            "{code}"
        );
    }
    for code in [
        "2.400 != 2.4",
        "i = 0",
        "1 / i = -1",
        "1 / (i - i) = 0",
        "1/3 != 2/6",
        "1/0 != 1",
    ] {
        assert!(
            exec_one(&mut runtime_with_file_env(), code).is_failed(),
            "{code}"
        );
    }
}

#[test]
fn aggregate_exact_nested_named_and_set_evaluation() {
    let mut rt = runtime_with_file_env();
    assert_eval_number(&mut rt, "eval sum(1,3,fn(k Z) Z {k})", "6");
    assert_eval_number(&mut rt, "eval product(1,3,fn(k Z) Z {k})", "6");
    assert_eval_number(&mut rt, "eval sum(1,3,fn(k Z) Q {1/3})", "1");
    assert_eval_number(
        &mut rt,
        "eval sum(1,3,fn(k N+) N+ {product(1,k,fn(j N+) N+ {j})})",
        "9",
    );
    assert!(!exec_one(&mut rt, "have fn square(k Z) Z = k*k").is_failed());
    assert_eval_number(&mut rt, "eval sum(1,3,square)", "14");
    assert_eval_number(&mut rt, "eval finite_set_product({1,2,3},square)", "36");
    assert!(
        exec_one(&mut rt, "eval finite_set_sum({1,1.00,2},fn(k Z) Z {k})").is_failed(),
        "list-set WD requires provably distinct elements, including normalized decimal aliases"
    );
    assert_eval_number(&mut rt, "eval finite_set_sum({},fn(k Z) Z {k})", "0");
    assert_eval_number(&mut rt, "eval finite_set_product({},fn(k Z) Z {k})", "1");
    for s in [
        "sum(1,3,square)=14",
        "product(1,3,square)=36",
        "sum(1,3,fn(x Z) Z {sum(1,2,fn(y Z) Z {x+y})})=21",
    ] {
        assert!(!exec_one(&mut rt, s).is_failed(), "{s}");
    }
}

#[test]
fn aggregate_domains_false_results_and_shared_budget_reject() {
    for s in [
        "sum(1,3,fn(k Z) Z {k})=7",
        "product(1,3,fn(k Z) Z {k})=7",
        "let bad = finite_set_sum({1},fn(k {2}) Z {k})",
        "let bad = finite_set_product({1},fn(k {2}) Z {k})",
        "eval sum(3,1,fn(k Z) Z {k})",
        "eval sum(-1,2,fn(k N) N {k})",
    ] {
        assert!(exec_one(&mut runtime_with_file_env(), s).is_failed(), "{s}");
    }
    for s in [
        "eval sum(1,1025,fn(k Z) Z {1})",
        "eval sum(1,32,fn(k Z) Z {sum(1,32,fn(j Z) Z {1})})",
    ] {
        assert!(
            matches!(
                exec_one(&mut runtime_with_file_env(), s),
                ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
                    ExecEvalStmtFailed::AggregateBudgetExceeded
                )))
            ),
            "{s}"
        );
    }
    assert!(matches!(exec_one(&mut runtime_with_file_env(), "eval sum(-170141183460469231731687303715884105727,170141183460469231731687303715884105727,fn(k Z) Z {1})"),
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(ExecEvalStmtFailed::AggregateRangeOverflow)))));
    let mut rt = runtime_with_file_env();
    assert!(exec_one(&mut rt, "let bad = finite_set_sum({1},fn(k {2}) Z {k})").is_failed());
    assert!(
        !rt.top_exec_env()
            .definitions
            .identifiers
            .contains_key("bad"),
        "failed execution must leave no runtime binding"
    );
}

#[test]
fn aggregate_symbolic_reindex_contract() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(&mut rt, "have f fn(k Z) R").is_failed());
    let code = "forall a,b,t Z:\n    a<=b\n    a+t<=b+t\n    =>:\n        sum(a,b,fn(k Z) R {f(k+t)})=sum(a+t,b+t,f)";
    let outcome = exec_one(&mut rt, code);
    assert!(
        !outcome.is_failed(),
        "{}",
        crate::json_output::project_stmt_detailed(&outcome, &rt).stringify_pretty()
    );
    assert!(!exec_one(&mut rt, "have n N+").is_failed());
    assert!(!exec_one(
        &mut rt,
        "forall:\n    3 <= n+2\n    =>:\n        sum(1,n,fn(k Z) R {f(k+2)}) = sum(3,n+2,f)"
    )
    .is_failed());
}

#[test]
fn aggregate_display_evidence_and_fact_publication_boundary() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(&mut rt, "have fn square(k Z) Z = k*k").is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let result = exec_one(&mut rt, "eval sum(1,3,square)");
    assert!(!result.is_failed());
    assert!(
        rt.top_exec_env().facts.facts_by_id.len() > before,
        "eval publishes its checked source=result equality"
    );
    let detail = crate::json_output::project_stmt_detailed(&result, &rt);
    let normal = crate::json_output::project_stmt_normal(&result, &rt);
    assert_eq!(
        normal
            .as_object()
            .unwrap()
            .get("evaluated_object")
            .unwrap()
            .as_str()
            .unwrap(),
        "14"
    );
    let aggregates = detail
        .as_object()
        .unwrap()
        .get("aggregate_evaluations")
        .unwrap();
    let JsonValue::Array(aggregates) = aggregates else {
        panic!("aggregate trace");
    };
    assert_eq!(aggregates.len(), 1);
    let aggregate = aggregates[0].as_object().unwrap();
    assert_eq!(aggregate.get("kind").unwrap().as_str().unwrap(), "sum");
    let JsonValue::Array(terms) = aggregate.get("terms").unwrap() else {
        panic!("terms");
    };
    assert_eq!(terms.len(), 3);
    let totals: Vec<_> = terms
        .iter()
        .map(|t| {
            t.as_object()
                .unwrap()
                .get("accumulated_value")
                .unwrap()
                .as_str()
                .unwrap()
        })
        .collect();
    assert_eq!(totals, vec!["1", "5", "14"]);
    assert!(terms[0]
        .as_object()
        .unwrap()
        .get("application_well_defined")
        .is_some());
    let direct = exec_one(&mut rt, "sum(1,3,square)=14");
    assert!(!direct.is_failed());
    assert!(
        rt.top_exec_env().facts.facts_by_id.len() > before,
        "direct equality owns proof publication"
    );
    let negative = exec_one(&mut rt, "sum(1,3,square)=15");
    assert!(negative.is_failed());
    let failed = exec_one(&mut rt, "eval sum(1,1025,square)");
    assert!(failed.is_failed());
    assert!(crate::json_output::project_stmt_normal(&failed, &rt)
        .stringify_pretty()
        .contains("aggregate_budget_exceeded"));
    assert!(crate::json_output::project_stmt_detailed(&failed, &rt)
        .stringify_pretty()
        .contains("aggregate_budget_exceeded"));
}

#[test]
fn aggregate_algorithm_terms_keep_checked_equations_and_eval_publishes_results() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(
        &mut rt,
        "algo flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1"
    )
    .is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    assert_eval_number(&mut rt, "eval sum(0,3,flag)", "3");
    assert!(rt.top_exec_env().facts.facts_by_id.len() > before);
    assert!(!exec_one(&mut rt, "sum(0,3,flag) = 3").is_failed());
    assert_eval_number(&mut rt, "eval product(1,3,flag)", "1");
    assert!(!exec_one(&mut rt, "product(1,3,flag) = 1").is_failed());
    assert_eval_number(&mut rt, "eval finite_set_sum({1/3,2/3},flag)", "2");
    assert!(!exec_one(&mut rt, "finite_set_sum({1/3,2/3},flag) = 2").is_failed());
    assert!(exec_one(&mut rt, "sum(0,3,flag) = 4").is_failed());
}

#[test]
fn eval_publishes_original_equality_and_preserves_failed_transaction_boundaries() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(&mut rt, "have a R = 10").is_failed());
    let outcome = exec_one(&mut rt, "eval a+1");
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(s))) =
        &outcome
    else {
        panic!("eval must succeed");
    };
    let fact: crate::ast::fact::Fact = s.evaluated_equal_fact.clone().into();
    assert_eq!(fact.readable_string(), "a + 1 = 11");
    let id = s.evaluated_equal_fact.fact_id;
    assert!(rt.top_exec_env().facts.facts_by_id.contains_key(&id));
    assert_eq!(s.store_and_infer_result.primary_fact_id(), id);
    let normal = crate::json_output::project_stmt_normal(&outcome, &rt);
    assert!(normal
        .as_object()
        .unwrap()
        .get("stores")
        .unwrap()
        .stringify_pretty()
        .contains("a + 1 = 11"));
    let detailed = crate::json_output::project_stmt_detailed(&outcome, &rt).stringify_pretty();
    assert!(detailed.contains(&id.to_string()));
    assert!(detailed.contains("store_and_infer"));
    let use_result = exec_one(&mut rt, "a+1=11");
    assert!(!use_result.is_failed());
    assert!(crate::json_output::project_stmt_detailed(&use_result, &rt)
        .stringify_pretty()
        .contains(&id.to_string()));

    let before = rt.top_exec_env().facts.facts_by_id.len();
    for code in ["eval 1/0", "eval sum(1,1025,fn(k Z) Z {k})", "a+1=12"] {
        assert!(exec_one(&mut rt, code).is_failed(), "{code}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before, "{code}");
    }
    assert!(exec_one(&mut rt, "claim:\n    ? 0=1\n    eval 20+3").is_failed());
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    assert!(!exec_one(&mut rt, "sketch:\n    eval 20+3").is_failed());
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
}

#[test]
fn eval_algorithm_trace_checks_nested_arguments_and_recursive_equations() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AlgoDefinitionEvidence;
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(
        &mut rt,
        "algo flag(x R) R by cases:\n    case x=0:0\n    case x!=0:1"
    )
    .is_failed());
    let result = exec_one(&mut rt, "eval flag(sum(0,3,flag))");
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(s))) =
        result
    else {
        panic!("nested algorithm evaluation must succeed");
    };
    assert!(!s.algo_evaluations.is_empty());
    assert!(s
        .algo_evaluations
        .iter()
        .all(|p| matches!(p.definition_evidence, AlgoDefinitionEvidence::Checked(_))));
    assert!(!exec_one(&mut rt, "flag(sum(0,3,flag))=1").is_failed());
    assert!(exec_one(&mut rt, "flag(sum(0,3,flag))=0").is_failed());
    assert!(!exec_one(
        &mut rt,
        "algo countdown(n N) N by induc n from 0:\n    case n=0:0\n    case n>=1:countdown(n-1)"
    )
    .is_failed());
    assert_eval_number(&mut rt, "eval countdown(4)", "0");
    assert!(!exec_one(&mut rt, "countdown(4)=0").is_failed());
}

#[test]
fn eval_publication_and_failure_are_visible_in_every_output_language() {
    use crate::json_output::json_keys::localize_key;
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language,
        });
        let result = exec_one(&mut rt, "eval 1+2");
        let normal = crate::json_output::project_stmt_normal(&result, &rt);
        let stores = normal
            .as_object()
            .unwrap()
            .get(&localize_key("stores", language))
            .unwrap();
        assert!(
            stores.stringify_pretty().contains("1 + 2 = 3"),
            "{language:?}"
        );
        let detail = crate::json_output::project_stmt_detailed(&result, &rt);
        assert!(detail
            .as_object()
            .unwrap()
            .get(&localize_key("fact_id", language)).is_some());
        assert!(!exec_one(&mut rt, "1+2=3").is_failed());
        let failed = exec_one(&mut rt, "eval 1/0");
        assert!(failed.is_failed());
        let normal = crate::json_output::project_stmt_normal(&failed, &rt);
        assert_eq!(
            normal
                .as_object()
                .unwrap()
                .get(&localize_key("stores", language))
                .unwrap(),
            &JsonValue::Array(vec![])
        );
    }
}

#[test]
fn aggregate_callable_predicates_and_scalar_carriers() {
    for code in [
        "eval sum(1,3,fn(k Z:k!=0) Z {1})",
        "eval finite_set_sum({1,2},fn(k Z:k!=0) Z {1})",
        "eval finite_set_sum({},fn(k Z:k!=0) R {1/k})",
        "product(1,3,fn(k N+) N+ {k}) $in N+",
    ] {
        assert!(
            !exec_one(&mut runtime_with_file_env(), code).is_failed(),
            "{code}"
        );
    }
    for code in [
        "let bad = sum(0,3,fn(k Z:k!=0) Z {1})",
        "let bad = finite_set_sum({1},fn(k Z:k!=1) Z {0})",
        "sum(1,1,fn(k Z) C {i}) $in R",
        "finite_set_sum({},fn(k N+) N+ {k}) $in N+",
    ] {
        assert!(
            exec_one(&mut runtime_with_file_env(), code).is_failed(),
            "{code}"
        );
    }
}

#[test]
fn eval_after_closed_numeric_equal_rewrite() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 10").is_failed());
    let outcome = exec_one(&mut runtime, "eval a + 1");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
            success,
        ))) => {
            assert_eq!(success.cited_equal_fact_ids.len(), 1);
            match success.evaluated_object {
                Obj::Literal(Literal::Number(Number { normalized_value })) => {
                    assert_eq!(normalized_value, "11");
                }
                other => panic!("expected number 11, got {other:?}"),
            }
        }
        other => panic!(
            "expected eval Success after rewrite, failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn eval_algo_call_and_nested_arithmetic() {
    let mut runtime = runtime_with_file_env();
    let algo = "algo nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1";
    assert!(!exec_one(&mut runtime, algo).is_failed());
    assert_eval_number(&mut runtime, "eval nonzero_flag(0)", "0");
    assert_eval_number(&mut runtime, "eval nonzero_flag(1)", "1");
    assert_eval_number(&mut runtime, "eval nonzero_flag(0) + 1", "1");
}

#[test]
fn eval_factorial_sqrt_log_closed_numeric_succeed() {
    let mut runtime = runtime_with_file_env();
    assert_eval_number(&mut runtime, "eval 2!", "2");
    assert_eval_number(&mut runtime, "eval 3!", "6");
    assert_eval_number(&mut runtime, "eval sqrt(4)", "2");
    let result = exec_one(&mut runtime, "eval sqrt(0.36)");
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(s))) =
        result
    else {
        panic!("exact rational sqrt must succeed");
    };
    assert_eq!(s.evaluated_object.readable_string(), "3 / 5");
    assert!(!exec_one(&mut runtime, "sqrt(0.36)=3/5").is_failed());
    assert_eval_number(&mut runtime, "eval log(2, 8)", "3");
}

#[test]
fn eval_non_square_sqrt_keeps_exact_root_and_publishes_equality() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "eval sqrt(2)");
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(s))) =
        outcome
    else {
        panic!("exact principal root must succeed");
    };
    assert_eq!(s.evaluated_object, s.source_object);
    assert!(runtime
        .top_exec_env()
        .facts
        .facts_by_id
        .contains_key(&s.evaluated_equal_fact.fact_id));
    assert!(exec_one(&mut runtime, "sqrt(2)=2").is_failed());
}

#[test]
fn eval_standard_set_soft_fails() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "eval N");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::UnsupportedExpression,
        ))) => {}
        other => panic!(
            "expected UnsupportedExpression, failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn eval_tuple_calls_compute_and_publish_without_prior_coordinate_equalities() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(&mut rt, "let p=(1,2,3)").is_failed());
    assert_eval_number(&mut rt, "eval p(2)", "2");
    assert!(!exec_one(&mut rt, "p(2)=2").is_failed());
    assert!(!exec_one(&mut rt, "have outer cart(cart(R,R),R)=((1,2),3)").is_failed());
    assert_eval_number(&mut rt, "eval outer(1)(2)", "2");
    assert!(!exec_one(&mut rt, "outer(1)(2)=2").is_failed());
    assert!(!exec_one(&mut rt, "let literal_outer=((1,2),3)").is_failed());
    assert_eval_number(&mut rt, "eval literal_outer(1)(2)", "2");
    for code in ["eval p(4)", "eval p(0)", "eval p(1,2)", "eval outer(2)(1)", "eval outer(1)(3)"] {
        let count = rt.top_exec_env().facts.facts_by_id.len();
        assert!(exec_one(&mut rt, code).is_failed(), "{code}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count, "failed eval published: {code}");
    }
    assert!(exec_one(&mut rt, "p(2)=3").is_failed());
}

#[test]
fn eval_tuple_coordinate_evidence_and_unknown_values_stay_checked() {
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(), session: false, strict: true, language,
        });
        assert!(!exec_one(&mut rt, "let p=(1,2,3)").is_failed());
        let result = exec_one(&mut rt, "eval p(2)");
        assert!(!result.is_failed());
        let detailed = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("finite_function_coordinate"), "{detailed}");
        assert!(detailed.contains("p(2)") && detailed.contains("tuple_equality"), "missing coordinate source: {detailed}");
        assert!(!exec_one(&mut rt, "have unknown cart(R,R)").is_failed());
        let count = rt.top_exec_env().facts.facts_by_id.len();
        assert!(exec_one(&mut rt, "eval unknown(1)").is_failed());
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
    }
}
