//! Finite inclusion rules must compose through WD and retain their premises.
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactResult;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::{ExecFactStmtResult, ExecFactStmtSuccessResult, ExecStmtResult};
use crate::json_output::{project_stmt_detailed, project_stmt_normal, stringify_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn exec(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .expect("tokenize");
    let stmts = rt.parse(&tokens).expect("parse");
    let mut last = None;
    for stmt in stmts {
        if let Some(previous) = &last {
            assert!(!ExecStmtResult::is_failed(previous), "setup failed: {code}");
        }
        last = Some(rt.exec_stmt(&stmt).expect("exec_stmt"));
    }
    last.expect("nonempty program")
}

fn assert_outcome(code: &str, accepted: bool) {
    let mut rt = runtime(OutputLanguage::English);
    let result = exec(&mut rt, code);
    assert_eq!(
        !result.is_failed(),
        accepted,
        "{code}\n{}",
        stringify_normal(&project_stmt_normal(&result, &rt))
    );
}

fn find_field<'a>(value: &'a JsonValue, key: &str, expected: &str) -> Option<&'a JsonValue> {
    match value {
        JsonValue::Object(map) => {
            if map.get(key).and_then(|v| v.as_str().ok()) == Some(expected) {
                return Some(value);
            }
            map.keys_in_order()
                .iter()
                .find_map(|k| find_field(map.get(k).unwrap(), key, expected))
        }
        JsonValue::Array(values) => values.iter().find_map(|v| find_field(v, key, expected)),
        _ => None,
    }
}

fn contains_key(value: &JsonValue, key: &str) -> bool {
    match value {
        JsonValue::Object(map) => {
            map.get(key).is_some()
                || map
                    .keys_in_order()
                    .iter()
                    .any(|k| contains_key(map.get(k).unwrap(), key))
        }
        JsonValue::Array(values) => values.iter().any(|v| contains_key(v, key)),
        _ => false,
    }
}

// Project the actual proved conclusion, without executing or inventing evidence.
fn last_conclusion(result: ExecStmtResult) -> ExecStmtResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = result else {
        panic!("fact success")
    };
    let VerifyFactResult::ForallFact(forall) = success.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(proof) = *forall else {
        panic!("forall success")
    };
    let crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactProof::ByLocalIntroduction(mut proof) = proof else {
        panic!("fresh forall must use local introduction");
    };
    let conclusion = proof.proved_then_facts.pop().expect("conclusion");
    ExecStmtResult::Fact(ExecFactStmtResult::Success(ExecFactStmtSuccessResult {
        verify_result: conclusion.verify_result,
        store_and_infer_result: conclusion.store_and_infer,
    }))
}

const EQUAL_SIZE: &str = "forall A set, B finite_set:\n    A $subset B\n    finite_set_size(A) = finite_set_size(B)\n    =>:\n        A = B\n";
const WEAK_SIZE: &str = "forall A set, B finite_set:\n    A $subset B\n    =>:\n        finite_set_size(A) <= finite_set_size(B)\n";
const STRICT_SIZE: &str = "forall A set, B finite_set:\n    A $subset B\n    A != B\n    =>:\n        finite_set_size(A) < finite_set_size(B)\n";
const NAMED_STRICT_SIZE: &str = "forall A set, B finite_set:\n    A $proper_subset B\n    =>:\n        finite_set_size(A) < finite_set_size(B)\n";

#[test]
fn finite_set_cardinality_rule_symbolic_composition() {
    for code in [
        "forall A set, B finite_set:\n    A $subset B\n    =>:\n        $is_finite_set(A)\n        finite_set_size(A) <= finite_set_size(B)\n",
        EQUAL_SIZE, WEAK_SIZE, STRICT_SIZE, NAMED_STRICT_SIZE,
        "forall A, B finite_set:\n    A $subset B\n    finite_set_size(B) = finite_set_size(A)\n    =>:\n        B = A\n",
        // A derived singleton theorem needs only explicit existing interfaces.
        "forall A finite_set, a A:\n    finite_set_size(A) = 1\n    =>:\n        {a} $subset A\n        finite_set_size({a}) = 1\n        finite_set_size({a}) = finite_set_size(A)\n        A = {a}\n",
    ] { assert_outcome(code, true); }
}

#[test]
fn finite_set_cardinality_rule_finiteness_order_alias_and_candidate_fallback() {
    for code in [
        "forall A, B set:\n    A $subset B\n    $is_finite_set(B)\n    =>:\n        $is_finite_set(A)\n",
        "forall A, B set:\n    $is_finite_set(B)\n    A $subset B\n    =>:\n        $is_finite_set(A)\n",
        "forall A, B set, F finite_set:\n    A $subset B\n    B $subset F\n    =>:\n        $is_finite_set(A)\n",
        "forall A, B set, F finite_set:\n    A = B\n    B $subset F\n    =>:\n        $is_finite_set(A)\n",
        "forall A set, B finite_set:\n    B $superset A\n    =>:\n        $is_finite_set(A)\n",
        "forall A set, B finite_set:\n    B $proper_superset A\n    =>:\n        $is_finite_set(A)\n",
        // An unusable infinite upper set must not mask a finite witness.
        "forall A set, B finite_set:\n    A $subset R\n    A $subset B\n    =>:\n        $is_finite_set(A)\n",
    ] { assert_outcome(code, true); }
}

#[test]
fn finite_set_cardinality_rule_rejects_missing_and_reversed_premises() {
    for code in [
        "forall A, B finite_set:\n    finite_set_size(A) = finite_set_size(B)\n    =>:\n        A = B\n",
        "forall A, B finite_set:\n    A $subset B\n    =>:\n        finite_set_size(A) < finite_set_size(B)\n",
        "forall A, B finite_set:\n    A != B\n    =>:\n        finite_set_size(A) < finite_set_size(B)\n",
        "forall A finite_set, B set:\n    A $subset B\n    =>:\n        $is_finite_set(B)\n",
        "forall A finite_set, B set:\n    A $subset B\n    =>:\n        finite_set_size(A) <= finite_set_size(B)\n",
        "forall A, B set:\n    A $subset B\n    B $subset A\n    =>:\n        $is_finite_set(A)\n",
        "forall A, B set, F finite_set:\n    A $subset B\n    =>:\n        $is_finite_set(A)\n",
        "have A set\n$is_finite_set(A)",
        "let n = finite_set_size(R)",
        "{1} = {2}",
        "finite_set_size({1}) < finite_set_size({1})",
    ] { assert_outcome(code, false); }
}

#[test]
fn finite_set_cardinality_rule_scope_and_failed_fact_do_not_leak() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, EQUAL_SIZE).is_failed());
    assert!(exec(&mut rt, "forall A, B finite_set:\n    finite_set_size(A) = finite_set_size(B)\n    =>:\n        A = B\n").is_failed());
    assert!(!exec(&mut rt, "have A set\nhave B set").is_failed());
    assert!(exec(&mut rt, "A = B").is_failed());
    assert!(exec(&mut rt, "$is_finite_set(A)").is_failed());
    assert!(exec(&mut rt, "$is_finite_set(A)").is_failed());
    assert!(exec(&mut rt, "let n = finite_set_size(A)").is_failed());
}

#[test]
fn finite_set_cardinality_rule_strategy_budget_is_consumed_without_truth_storage() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have A set = intersect({1}, R)\nA $subset {1}").is_failed());
    let tokens = Tokenizer::new()
        .tokenize("$is_finite_set(A)", rt.current_file.clone())
        .unwrap();
    let stmt = rt.parse(&tokens).unwrap().pop().unwrap();
    let Stmt::Fact(fact) = stmt else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&fact, VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    assert!(!rt
        .verify_fact(&fact, VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::Strategy))
        .unwrap()
        .is_failed());
    // Verification alone must not cache truth and bypass a subsequent budget.
    assert!(rt
        .verify_fact(&fact, VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
}

#[test]
fn finite_set_cardinality_rule_detailed_retains_winning_route_and_premises() {
    for (code, rule, expected_keys, route) in [
        (
            EQUAL_SIZE,
            "FiniteSetEqualFromSubsetSize",
            vec!["size_equal_proof", "subset_proof"],
            None,
        ),
        (
            WEAK_SIZE,
            "FiniteSetSizeSubsetLe",
            vec!["subset_proof"],
            None,
        ),
        (
            STRICT_SIZE,
            "FiniteSetSizeProperSubsetLt",
            vec!["subset_proof", "not_equal_proof"],
            Some("BySubsetAndNotEqual"),
        ),
        (
            NAMED_STRICT_SIZE,
            "FiniteSetSizeProperSubsetLt",
            vec!["proper_subset_proof"],
            Some("ByProperSubset"),
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, code);
        assert!(!result.is_failed(), "{code}");
        let detailed = project_stmt_detailed(&result, &rt);
        let node = find_field(&detailed, "rule", rule).expect("winning rule");
        for key in expected_keys {
            assert!(contains_key(node, key), "{rule}: {key}");
        }
        assert!(
            contains_key(node, "cite_fact_id"),
            "must cite checked source premises"
        );
        if let Some(route) = route {
            assert!(find_field(node, "route", route).is_some());
        }
        // Cardinality WD retains finite-set evidence even when A was just `set`.
        assert!(contains_key(&detailed, "well_defined"));
    }
    let mut rt = runtime(OutputLanguage::English);
    let result = exec(
        &mut rt,
        "have A set = intersect({1}, R)\nA $subset {1}\n$is_finite_set(A)",
    );
    assert!(!result.is_failed());
    let detailed = project_stmt_detailed(&result, &rt);
    let node = find_field(&detailed, "strategy", "SubsetOfFiniteSet").expect("subset strategy");
    assert!(contains_key(node, "proof_of_requirement_facts"));
    assert!(contains_key(node, "cite_fact_id"));
}

#[test]
fn finite_set_cardinality_rule_normal_explains_actual_certificates_in_both_languages() {
    for (language, equal_label, strict_label) in [
        (
            OutputLanguage::English,
            "Equal finite subset cardinality",
            "Proper finite subset cardinality",
        ),
        (
            OutputLanguage::Chinese,
            "有限子集等大则相等",
            "有限真子集的基数严格更小",
        ),
    ] {
        for (code, label) in [
            (EQUAL_SIZE, equal_label),
            (STRICT_SIZE, strict_label),
            (NAMED_STRICT_SIZE, strict_label),
        ] {
            let mut rt = runtime(language);
            let result = exec(&mut rt, code);
            assert!(!result.is_failed());
            let conclusion = last_conclusion(result);
            let normal = project_stmt_normal(&conclusion, &rt);
            let text = stringify_normal(&normal);
            // Chinese Normal localizes field names as well as the explanation.
            assert!(text.contains(label), "{label}: {text}");
        }
    }
}
