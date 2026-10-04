# src basic audit: tests/unit/execute/showcase_local_rules/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## cosine_integer_offset_positive_and_evidence

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn cosine_integer_offset_positive_and_evidence() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_strategy/cos_zero_integer_offset.lit"
        )),
        true,
    );
    assert!(detailed.contains("CosZeroIntegerOffset"));
    assert!(detailed.contains("PeriodicTrig"));
    assert!(detailed.contains("proof_of_requirement_facts"));
    // Numeric/integral angles now take the direct periodic leaf. A symbolic
    // denominator still exercises the original guarded strategy and evidence.
    let guarded = check("have a R:\n    a != 0\ncos(a*pi/a+pi/2)=0", true);
    assert!(guarded.contains("RationalWithNonzeroPremises"));
    assert!(guarded.contains("PiNonzero"));
    check("0 = cos(3*pi/2)", true);
}
```

Observed failure excerpt:

```text
thread 'execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::cosine_integer_offset_positive_and_evidence' (71852635) panicked at src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/../../../../../tests/unit/execute/showcase_local_rules/tests.rs:32:5:
assertion `left == right` failed: have a R:
    a != 0
cos(a*pi/a+pi/2)=0
{
  "kind": "run",
  "success": false,
  "target": "showcase local rules",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "kind": "have_obj_by_exist_facts",
      "statement": "have a R:\n    a != 0",
      "store_and_infer": {
        "stores": [
          {
            "fact_id": "f5",
            "fact": "a $in R"
          },
          {
            "fact_id": "f1",
            "fact": "a != 0"
          }
        ],
        "infers": []
      }
    },
    {
      "success": false,
      "kind": "fact",
      "statement": "cos(a * pi / a + pi / 2) = 0",
      "verify": {
        "type": "equality",
        "success": false,
        "phase": "search_proof",
        "fact": "cos(a * pi / a + pi / 2) = 0",
        "well_defined": {
          "left": {
            "type": "by_def",
            "family": "TrigOperator",
            "kind": "Cos",
            "obj": "cos(a * pi / a + pi / 2)",
            "child_obj_well_defined": [
              {
                "type": "by_def",
                "family": "ArithmeticOperator",
                "kind": "Add",
                "obj": "a * pi / a + pi / 2",
                "child_obj_well_defined": [
                  {
                    "type": "by_def",
                    "family": "ArithmeticOperator",
                    "kind": "Div",
                    "obj": "a * pi / a"
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::cosine_integer_offset_positive_and_evidence -- --exact --nocapture
```

## full_add2_chain_and_projection_boundaries

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn full_add2_chain_and_projection_boundaries() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit"
        )),
        true,
    );
    for node in [
        "TupleComponentEquality",
        "ArithmeticCongruence",
        "LiteralTupleProjectionMembership",
        "TupleComponentAtIndex",
    ] {
        assert!(detailed.contains(node), "{node}");
    }
    let definition = "have fn add2(u,v cart(R,R)) cart(R,R)=(u[1]+v[1],u[2]+v[2])\n";
    check(
        &format!("{definition}add2((1,2),(3,4))=(1+3,2+4)=(4,7)"),
        false,
    );
    check(&format!("{definition}add2((1,2,3),(3,4))=(4,6)"), false);
    for code in [
        "(1,-2)[2] $in N",
        "(1,2)[0]=1",
        "(1,2)[3]=1",
        "(1/0+1,2)=(1/0+1,2)",
        "1+2=1*2",
    ] {
        check(code, false);
    }
}
```

Observed failure excerpt:

```text
thread 'execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::full_add2_chain_and_projection_boundaries' (71852640) panicked at src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/../../../../../tests/unit/execute/showcase_local_rules/tests.rs:32:5:
assertion `left == right` failed: # Before: the full call timed out; literal projection carriers were unavailable.
# Now: unfold the function, prove coordinates, then calculate tuple entries.
# Gate: target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit
have fn add2(u, v cart(R, R)) cart(R, R) = (u[1] + v[1], u[2] + v[2])
add2((1, 2), (3, 4)) = (1 + 3, 2 + 4) = (4, 6)

{
  "kind": "run",
  "success": false,
  "target": "showcase local rules",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "kind": "have_fn_equal",
      "statement": "have fn add2(u, v cart(R, R)) = (u[1] + v[1], u[2] + v[2])",
      "anonymous_fn_well_defined": {
        "success": true,
        "proof": {
          "type": "by_def",
          "family": "FunctionSpace",
          "kind": "AnonymousFn",
          "obj": "fn (u, v cart(R, R)) cart(R, R){(u[1] + v[1], u[2] + v[2])}",
          "param_type_well_defined": [
            {
              "type": "by_def",
              "family": "ProductShape",
              "kind": "Cart",
              "obj": "cart(R, R)",
              "child_obj_well_defined": [
                {
                  "type": "by_def",
                  "family": "StandardSet",
                  "kind": "StandardSet",
                  "obj": "R"
                },
                {
                  "type": "by_def",
                  "family": "StandardSet"
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::full_add2_chain_and_projection_boundaries -- --exact --nocapture
```

