# src basic audit: tests/unit/execute/showcase_local_repairs/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## positive_natural_predecessor_keeps_both_cited_premises_and_allows_recursion

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn positive_natural_predecessor_keeps_both_cited_premises_and_allows_recursion() {
    let detail = check(include_str!("../../../../examples/wd/positive_natural_predecessor.lit"), true);
    assert!(detail.contains("PredecessorFromPositiveNatural"));
    assert!(detail.contains("in_natural_proof") && detail.contains("positive_proof"));
    check("forall n N:\n    n >= 1\n    =>:\n        n - 1 $in N", true);
    check("forall n N:\n    0 < n\n    =>:\n        n - 1 $in N", true);
    for source in [
        "0 - 1 $in N", "(1 / 2) - 1 $in N",
        "forall n N:\n    n - 1 $in N",
        "forall x R:\n    x > 0\n    =>:\n        x - 1 $in N",
        "forall n Z:\n    n < 0\n    =>:\n        n - 1 $in N",
    ] { check(source, false); }
}
```

Observed failure excerpt:

```text
thread 'execute::showcase_local_repair_tests::positive_natural_predecessor_keeps_both_cited_premises_and_allows_recursion' (71852909) panicked at src/execute/../../tests/unit/execute/showcase_local_repairs/tests.rs:16:5:
# Showcase migration regression: verified without trust.
# Run: target/release/litex -strict -f examples/wd/positive_natural_predecessor.lit
# A positive natural has a natural predecessor, including in recursion WD.
forall n N:
    n > 0
    =>:
        n - 1 $in N

have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: countdown(n - 1)

countdown(0) = 0
countdown(1) = 0

# Reversed order has its own cited builtin route.
forall n N:
    0 < n
    =>:
        n - 1 $in N

Some(Runtime(ParseError(RuntimeParseError { message: "undefined name `countdown`", line: 13, path: Eval })))
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::showcase_local_repair_tests::positive_natural_predecessor_keeps_both_cited_premises_and_allows_recursion -- --exact --nocapture
```

## declared_field_types_close_nested_calls_without_releasing_laws

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn declared_field_types_close_nested_calls_without_releasing_laws() {
    let detail = check(FIELD, true);
    assert!(detail.contains("FieldApplicationInDeclaredCodomain"));
    assert!(detail.contains("FieldInDeclaredSet"));
    for goal in [
        "s.add(s.add(i, 0), 0) $in R",
        "s.add(s.add(0, 0), 0) $in N",
        "s.add(s.add(0, 0), 0) = 1",
    ] {
        check(&format!("{FIELD}\nthm bad:\n    ? forall s &Operation<R>:\n        {goal}"), false);
    }
    check("struct Guarded<A nonempty_set, zero A>:\n    tag N\n    call fn(x A: x != zero) A\nthm bad:\n    ? forall s &Guarded<R, 0>:\n        s.call(s.call(0)) $in R", false);
}
```

Observed failure excerpt:

```text
thread 'execute::showcase_local_repair_tests::declared_field_types_close_nested_calls_without_releasing_laws' (71852907) panicked at src/execute/../../tests/unit/execute/showcase_local_repairs/tests.rs:47:5:
assertion failed: detail.contains("FieldInDeclaredSet")
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::showcase_local_repair_tests::declared_field_types_close_nested_calls_without_releasing_laws -- --exact --nocapture
```

## unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd() {
    let detail = check(TEMPLATE, true);
    assert!(detail.contains("template_definition"));
    assert!(detail.contains("TemplateApplicationInDeclaredCodomain"));
    check(&format!("{TEMPLATE}\nthm bad:\n    ? forall t &Point<N, R>:\n        \\selected_value<Z, R, t>(0) = t.value"), false);
    check(&format!("{TEMPLATE}\nthm bad:\n    ? forall t, u &Point<N, R>:\n        \\selected_value<N, R, t>(0) = u.value"), false);
    // A template guard is checked even when its result is a nested argument.
    let guarded = "template<S set: $is_nonempty_set(S)>:\n    have fn guarded_identity(x R) R = x\nhave fn identity(x R) R = x\n";
    check(&format!("{guarded}\nthm good:\n    ? forall S nonempty_set:\n        identity(\\guarded_identity<S>(0)) $in R"), true);
    check(&format!("{guarded}\nthm bad:\n    ? forall S set:\n        identity(\\guarded_identity<S>(0)) $in R"), false);
}
```

Observed failure excerpt:

```text
thread 'execute::showcase_local_repair_tests::unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd' (71852911) panicked at src/execute/../../tests/unit/execute/showcase_local_repairs/tests.rs:17:5:
assertion `left == right` failed: # Showcase migration regression: verified without trust.
# Run: target/release/litex -strict -f examples/wd/template_unique_from_typed_carrier.lit
# Recover S from the already matched t : Point<S> when using a theorem.
struct Point<K nonempty_set, S nonempty_set>:
    value S
    tag N

thm unique_value:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        exist! x S st {x = t.value}
    witness exist! x S st {x = t.value} from t.value

template<K nonempty_set, S nonempty_set, t &Point<K, S>>:
    have fn selected_value by exist!:
        ? forall index N:
            exist! x S st {x = t.value}

thm selected_value_spec:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        \selected_value<K, S, t>(0) = t.value

struct Unary<S nonempty_set>:
    call fn(x S) S
    tag N

# The template occurs under another call, whose WD uses read-only premises.
thm selected_value_nested:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>, op &Unary<S>:
        op.call(\selected_value<K, S, t>(0)) $in S

thm bad:
    ? forall t &Point<N, R>:
        \selected_value<Z, R, t>(0) = t.value
  left: true
 right: false
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::showcase_local_repair_tests::unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd -- --exact --nocapture
```

## original_showcase_sections_use_the_repaired_paths

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn original_showcase_sections_use_the_repaired_paths() {
    let linear = include_str!("../../../../showcases/math_concepts_in_litex/5_linear_algebra/main.lit");
    check(linear.split("thm injective_linear_map_has_trivial_kernel:").next().unwrap(), true);
    let group = include_str!("../../../../showcases/math_concepts_in_litex/6_abstract_algebra/main.lit");
    check(group.split("thm ring_homomorphism_kernel_is_ideal:").next().unwrap(), true);
    let topology = include_str!("../../../../showcases/math_concepts_in_litex/9_topology/main.lit");
    check(topology.split("thm continuous_image_of_compact_is_compact:").next().unwrap(), true);
    let newton = include_str!("../../../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit");
    check(newton.split("thm newton_sqrt_two_residual_identity:").next().unwrap(), true);
}
```

Observed failure excerpt:

```text
thread 'execute::showcase_local_repair_tests::original_showcase_sections_use_the_repaired_paths' (71852908) panicked at src/execute/../../tests/unit/execute/showcase_local_repairs/tests.rs:17:5:
assertion `left == right` failed: # Draft: excluded from the published showcase gate until it verifies again.
# Linear algebra begins with a scalar field and a vector space over that field.
# Coordinate spaces appear later as instances of these interfaces.
#
# Included: first-class field and vector-space structures, linear maps and
# kernels, the trivial-kernel criterion for injectivity, concrete R and R^2
# instances, and the projection onto the x-axis.

# A field packages scalar operations together with the laws used below.
struct Field<K nonempty_set>:
    zero K
    one K
    add fn(x, y K) K
    neg fn(x K) K
    mul fn(x, y K) K
    inv fn(x K) K
    <=>:
        zero != one
        forall x, y, z K:
            add(add(x, y), z) = add(x, add(y, z))
            mul(mul(x, y), z) = mul(x, mul(y, z))
            mul(x, add(y, z)) = add(mul(x, y), mul(x, z))
        forall x, y K:
            add(x, y) = add(y, x)
            mul(x, y) = mul(y, x)
        forall x K:
            add(zero, x) = x
            add(x, neg(x)) = zero
            mul(one, x) = x
        forall x K:
            x != zero
            =>:
                mul(x, inv(x)) = one

# A vector space over one fixed scalar field stores its vector operations and
# compatibility laws as one first-class object.

struct VectorSpace<K nonempty_set, field &Field<K>, V nonempty_set>:
    zero V
    add fn(x, y V) V
    smul fn(a K, x V) V
    <=>:
        forall x, y, z V:
            add(add(x, y), z) = add(x, add(y, z))
        forall x, y V:
            add(x, y) = add(y, x)
        forall x V:
            add(ze
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::showcase_local_repair_tests::original_showcase_sections_use_the_repaired_paths -- --exact --nocapture
```

