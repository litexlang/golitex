# src basic audit: tests/unit/execute/finite_set_cardinality_rules/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## finite_set_cardinality_rule_detailed_retains_winning_route_and_premises

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
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
```

Observed failure excerpt:

```text
thread 'execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_detailed_retains_winning_route_and_premises' (71852688) panicked at src/execute/../../tests/unit/execute/finite_set_cardinality_rules/tests.rs:212:9:
forall A set, B finite_set:
    A $subset B
    =>:
        finite_set_size(A) <= finite_set_size(B)
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_detailed_retains_winning_route_and_premises -- --exact --nocapture
```

## finite_set_cardinality_rule_finiteness_order_alias_and_candidate_fallback

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
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
```

Observed failure excerpt:

```text
thread 'execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_finiteness_order_alias_and_candidate_fallback' (71852689) panicked at src/execute/../../tests/unit/execute/finite_set_cardinality_rules/tests.rs:39:5:
assertion `left == right` failed: forall A, B set, F finite_set:
    A $subset B
    B $subset F
    =>:
        $is_finite_set(A)

{
  "success": false,
  "statement": "forall A, B set, F finite_set:\n    A $subset B\n    B $subset F\n    =>:\n        $is_finite_set(A)",
  "why_failed": {
    "phase": "search_proof",
    "goal": "forall A, B set, F finite_set:\n    A $subset B\n    B $subset F\n    =>:\n        $is_finite_set(A)"
  },
  "stores": [],
  "infers": []
}
  left: false
 right: true
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_finiteness_order_alias_and_candidate_fallback -- --exact --nocapture
```

## finite_set_cardinality_rule_normal_explains_actual_certificates_in_both_languages

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
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
```

Observed failure excerpt:

```text
thread 'execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_normal_explains_actual_certificates_in_both_languages' (71852690) panicked at src/execute/../../tests/unit/execute/finite_set_cardinality_rules/tests.rs:261:13:
assertion failed: !result.is_failed()
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_normal_explains_actual_certificates_in_both_languages -- --exact --nocapture
```

## finite_set_cardinality_rule_symbolic_composition

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn finite_set_cardinality_rule_symbolic_composition() {
    for code in [
        "forall A set, B finite_set:\n    A $subset B\n    =>:\n        $is_finite_set(A)\n        finite_set_size(A) <= finite_set_size(B)\n",
        EQUAL_SIZE, WEAK_SIZE, STRICT_SIZE, NAMED_STRICT_SIZE,
        "forall A, B finite_set:\n    A $subset B\n    finite_set_size(B) = finite_set_size(A)\n    =>:\n        B = A\n",
        // A derived singleton theorem needs only explicit existing interfaces.
        "forall A finite_set, a A:\n    finite_set_size(A) = 1\n    =>:\n        {a} $subset A\n        finite_set_size({a}) = 1\n        finite_set_size({a}) = finite_set_size(A)\n        A = {a}\n",
    ] { assert_outcome(code, true); }
}
```

Observed failure excerpt:

```text
thread 'execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_symbolic_composition' (71852694) panicked at src/execute/../../tests/unit/execute/finite_set_cardinality_rules/tests.rs:39:5:
assertion `left == right` failed: forall A set, B finite_set:
    A $subset B
    =>:
        $is_finite_set(A)
        finite_set_size(A) <= finite_set_size(B)

{
  "success": false,
  "statement": "forall A set, B finite_set:\n    A $subset B\n    =>:\n        $is_finite_set(A)\n        finite_set_size(A) <= finite_set_size(B)",
  "why_failed": {
    "phase": "search_proof",
    "goal": "forall A set, B finite_set:\n    A $subset B\n    =>:\n        $is_finite_set(A)\n        finite_set_size(A) <= finite_set_size(B)"
  },
  "stores": [],
  "infers": []
}
  left: false
 right: true
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_symbolic_composition -- --exact --nocapture
```

