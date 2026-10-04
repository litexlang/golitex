# src basic audit: tests/unit/execute/showcase_regressions/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## induction_recovers_order_and_nested_arithmetic_binders

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn induction_recovers_order_and_nested_arithmetic_binders() {
    for goal in ["k >= k", "k <= k", "k $in Z", "2^k = 2^k", "(k + 1) * 2 = (k + 1) * 2", "k = k or k > k", "k = k = k"] {
        check(&format!("by induc k from 0:\n    ? {goal}\n"), true);
    }
    check("by induc k from 0:\n    ? not k > k\n    k <= k\n    k + 1 <= k + 1\n", true);
    check("by strong_induc k from 0:\n    ? k >= k\n", true);
}
```

Observed failure excerpt:

```text
thread 'execute::execute_by_stmt::showcase_regressions::induction_recovers_order_and_nested_arithmetic_binders' (71852463) panicked at src/execute/execute_by_stmt/../../../tests/unit/execute/showcase_regressions/tests.rs:10:5:
assertion `left == right` failed: by induc k from 0:
    ? not k > k
    k <= k
    k + 1 <= k + 1

{
  "kind": "run",
  "success": false,
  "target": "showcase regression",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": false,
      "kind": "by_induc",
      "failure": {
        "phase": "step",
        "failure": {
          "phase": "goal",
          "goal_index": 0,
          "result": {
            "type": "atomic_except_equality",
            "success": false,
            "phase": "search_proof",
            "fact": "not k + 1 > k + 1",
            "well_defined": {
              "well_defined_of_each_parameter": [
                {
                  "type": "by_known",
                  "obj": "k + 1",
                  "wd_id": "wd8"
                },
                {
                  "type": "by_known",
                  "obj": "k + 1",
                  "wd_id": "wd8"
                }
              ],
              "predicate_signature": {
                "type": "builtin"
              },
              "predicate_domain": [
                {
                  "requirement": "k + 1 $in R",
                  "verify": {
                    "type": "atomic_except_equality",
                    "success": true,
                    "fact": "k + 1 $in R",
                    "well_defined": {
                      "well_defined_of_each_parameter": [
                        {
                          "type": "by_known",
                          "obj": "k + 1",
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_by_stmt::showcase_regressions::induction_recovers_order_and_nested_arithmetic_binders -- --exact --nocapture
```

## showcase_exponential_induction_closes_successor_goal

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn showcase_exponential_induction_closes_successor_goal() {
    check(include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/stmt_nodes/by/by_induc_order.lit")), true);
}
```

Observed failure excerpt:

```text
thread 'execute::execute_by_stmt::showcase_regressions::showcase_exponential_induction_closes_successor_goal' (71852474) panicked at src/execute/execute_by_stmt/../../../tests/unit/execute/showcase_regressions/tests.rs:10:5:
assertion `left == right` failed: # Before (rejected by the previous implementation):
# by induc k from 0:
#     ? k >= k
# Now: the active proof below verifies without trust.
# Boundary: false base/step and noninteger starts remain rejected by showcase_regressions.
# Gate: target/release/litex -strict -f examples/stmt_nodes/by/by_induc_order.lit

by induc k from 0:
    ? k >= k

by strong_induc k from 0:
    ? k <= k

by induc k from 0:
    ? 2^k = 2^k

by induc k from 0:
    ? k = k or k > k

# Original showcase theorem: binder recovery, natural powers, and mixed order chains.
claim:
    ? forall n N:
        2^n >= n + 1
    by induc k from 0:
        ? 2^k >= k + 1
        ? from k = 0:
            2^0 = 1 >= 0 + 1
        ? induc:
            0 <= k
            0 <= k + 1
            k $in N
            1 $in N
            2 $in C
            2^(k + 1) = 2^k * 2^1
            2^1 = 2
            2^k * 2 >= (k + 1) * 2
            2^(k + 1) >= (k + 1) * 2 = (k + 1) + (k + 1) >= k + 1 + 1


{
  "kind": "run",
  "success": false,
  "target": "showcase regression",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "kind": "by_induc",
      "from_in_z": {
        "type": "atomic_except_equality",
        "success": true,
        "fact": "0 $in Z",
        "well_defined": {
          "well_defined_of_each_parameter": [
            {
              "type": "by_def",
              "family": "Literal",
              "kind": "Number",
              "obj": "0"
            },
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_by_stmt::showcase_regressions::showcase_exponential_induction_closes_successor_goal -- --exact --nocapture
```

## original_showcase_amgm_and_group_left_cancel

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn original_showcase_amgm_and_group_left_cancel() {
    check(include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/order/am_gm.lit")), true);
    check(include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/wd/fact/group_left_cancel.lit")), true);
}
```

Observed failure excerpt:

```text
thread 'execute::execute_by_stmt::showcase_regressions::original_showcase_amgm_and_group_left_cancel' (71852469) panicked at src/execute/execute_by_stmt/../../../tests/unit/execute/showcase_regressions/tests.rs:10:5:
assertion `left == right` failed: # Original showcase AM-GM proof, including the original contradiction argument.
# Previously 0 <= (x+y)/2 and real-order complementation blocked this proof.
# Denominator sign, real carriers, and nonnegative square operands are required.
# Gate: target/release/litex -strict -f examples/proof_nodes/order/am_gm.lit

have fn arithmetic_mean(x, y R) R = (x + y) / 2

claim:
    ? forall x, y R:
        x >= 0
        y >= 0
        =>:
            x * y >= 0
    0 <= x
    0 <= y
    0 <= x * y
have fn geometric_mean(x, y R: x >= 0, y >= 0) R = sqrt(x * y)

thm two_variable_am_gm:
    ? forall x, y R:
        x >= 0
        y >= 0
        =>:
            geometric_mean(x, y) <= arithmetic_mean(x, y)
    x * y >= 0
    0 <= x * y
    sqrt(x * y)^2 = x * y
    0 <= x
    0 <= y
    (x + y)^2 - 4 * x * y = (x - y)^2
    0 <= (x - y)^2
    0 <= (x + y)^2 - 4 * x * y
    4 * x * y <= (x + y)^2
    x * y = (4 * x * y) / 4 <= (x + y)^2 / 4
    ((x + y) / 2)^2 = (x + y)^2 / 4
    x * y <= ((x + y) / 2)^2
    0 <= sqrt(x * y)
    0 <= x + y
    0 < 2
    0 <= (x + y) / 2
    by contra:
        ? sqrt(x * y) <= (x + y) / 2
        sqrt(x * y) > (x + y) / 2
        sqrt(x * y)^2 > ((x + y) / 2)^2
        impossible x * y <= ((x + y) / 2)^2
    geometric_mean(x, y) = sqrt(x * y)
    arithmetic_mean(x, y) = (x + y) / 2


{
  "kind": "run",
  "success": false,
  "target": "showcase regression",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "kind": "have_fn_equal",
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_by_stmt::showcase_regressions::original_showcase_amgm_and_group_left_cancel -- --exact --nocapture
```

