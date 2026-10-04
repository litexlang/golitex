# src basic audit: tests/unit/execute/exact_numeric_periodic_modulus/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## rational_pi_order_and_inverse_principal_values

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn rational_pi_order_and_inverse_principal_values() {
    for source in [
        "(-pi)/2<pi/4",
        "pi/4<pi/2",
        "0<3*pi/4",
        "3*pi/4<pi",
        "(-3)*pi/4<(-pi)/2",
        "pi/4+pi/4<pi",
        "(-pi)/2 $in R\npi/2 $in R\npi/4 $in R\ncos(pi/4)!=0\ntan(pi/4)=1\n(-pi)/2<pi/4\npi/4<pi/2\narctan(1)=arctan(tan(pi/4))=pi/4",
        "(-pi)/2 $in R\npi/2 $in R\n(-pi)/4 $in R\ncos(-pi/4)!=0\ntan(-pi/4)=-1\n(-pi)/2<(-pi)/4\n(-pi)/4<pi/2\narctan(-1)=arctan(tan(-pi/4))=(-pi)/4",
        "0 $in R\npi $in R\npi/4 $in R\nsin(pi/4)!=0\ncot(pi/4)=1\n0<pi/4\npi/4<pi\narccot(1)=arccot(cot(pi/4))=pi/4",
        "0 $in R\npi $in R\n3*pi/4 $in R\nsin(3*pi/4)!=0\ncot(3*pi/4)=-1\n0<3*pi/4\n3*pi/4<pi\narccot(-1)=arccot(cot(3*pi/4))=3*pi/4",
    ] { check(source, true); }
    for source in [
        "pi/2<pi/4", "pi/4<pi/4", "pi/4<0",
        "arctan(tan(3*pi/4))=3*pi/4",
        "(-pi)/2 $in R\npi/2 $in R\n3*pi/4 $in R\ntan(3*pi/4)=-1\narctan(tan(3*pi/4))=3*pi/4",
        "arccot(cot(-pi/4))=-pi/4",
        "0 $in R\npi $in R\n(-pi)/4 $in R\ncot(-pi/4)=-1\narccot(cot(-pi/4))=-pi/4",
        "arccot(-1)=-pi/4", "arctan(1)=-pi/4",
        "arctan(tan(pi/2))=pi/2", "cot(0)=0", "cot(pi)=0",
        "have x R\nx*pi<pi", "pi/0<pi", "pi*pi<pi",
    ] { check(source, false); }
    let json = check("pi/4<pi/2", true);
    assert!(json.contains("PiMultipleComparison") && json.contains("left_coefficient"));
    let json = check("0 $in R\npi $in R\n3*pi/4 $in R\ncot(3*pi/4)=-1\n0<3*pi/4\n3*pi/4<pi\narccot(-1)=arccot(cot(3*pi/4))=3*pi/4", true);
    assert!(json.contains("ArccotCotRightInverse") && json.contains("proof_of_requirement_facts"), "{json}");
}
```

Observed failure excerpt:

```text
thread '<unnamed>' (71852229) panicked at src/execute/../../tests/unit/execute/exact_numeric_periodic_modulus/tests.rs:20:13:
assertion `left == right` failed: (-pi)/2<pi/4
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": false,
      "kind": "fact",
      "statement": "<wd_failed>",
      "verify": {
        "type": "atomic_except_equality",
        "success": false,
        "phase": "well_defined",
        "failure": {
          "phase": "predicate_domain",
          "completed_requirements": [],
          "requirement": "-pi / 2 $in R",
          "verify": {
            "type": "atomic_except_equality",
            "success": false,
            "phase": "search_proof",
            "fact": "-pi / 2 $in R",
            "well_defined": {
              "well_defined_of_each_parameter": [
                {
                  "type": "by_def",
                  "family": "ArithmeticOperator",
                  "kind": "Div",
                  "obj": "-pi / 2",
                  "child_obj_well_defined": [
                    {
                      "type": "by_def",
                      "family": "ArithmeticOperator",
                      "kind": "Neg",
                      "obj": "-pi",
                      "child_obj_well_defined": [
                        {
                          "type": "by_def",
                          "family": "Literal",
                          "kind": "Pi",
                          "obj": "pi"
                        }
                      ],
                      "requirement_fact_verified": [
                        {
                          "type": "atomic_except_equality",
                          "success": tru
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::exact_numeric_periodic_modulus::rational_pi_order_and_inverse_principal_values -- --exact --nocapture
```

## new_leaves_inherit_search_ceiling_and_do_not_store_search_facts

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn new_leaves_inherit_search_ceiling_and_do_not_store_search_facts() {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    use crate::tokenize::Tokenizer;
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(runtime.run_litex_code("have k Z\nlet rational_max = finite_set_max({1/3,1/2})").unwrap().success);
    for source in [
        "tan(pi+2*k*pi)=0",
        "C_abs(3-4*i)=5",
        "3^(-2)=1/9",
        "1/3<1/2",
        "finite_set_max({1/3,1/2})=1/2",
        "pi/4<pi/2",
        "e>1",
    ] {
        let tokens = Tokenizer::new()
            .tokenize(source, runtime.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = runtime.parse(&tokens).unwrap().remove(0) else {
            panic!("fact");
        };
        let memory = |rt: &Runtime| {
            rt.execution_environments_stack
                .iter()
                .map(|env| {
                    (
                        env.facts.facts_by_id.len(),
                        env.well_defined_objects.object_to_wd_id.len(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = memory(&runtime);
        let state = VerifyState::new(VerifyStateLevel::BuiltinRule);
        assert!(
            !runtime
                .verify_fact(&fact, state.clone())
                .unwrap()
                .is_failed(),
            "{source}"
        );
        assert_eq!(
            before,
            memory(&runtime),
            "successful search is read-only: {source}"
        );
        let state = state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        assert!(
            runtime.verify_fact(&fact, state).unwrap().is_failed(),
            "disabled builtin: {source}"
        );
        assert_eq!(
            before,
            memory(&runtime),
            "failed search is read-only: {source}"
        );
    }
}
```

Observed failure excerpt:

```text
thread 'execute::exact_numeric_periodic_modulus::new_leaves_inherit_search_ceiling_and_do_not_store_search_facts' (71852187) panicked at src/execute/../../tests/unit/execute/exact_numeric_periodic_modulus/tests.rs:291:9:
tan(pi+2*k*pi)=0
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::exact_numeric_periodic_modulus::new_leaves_inherit_search_ceiling_and_do_not_store_search_facts -- --exact --nocapture
```

## new_rule_normal_output_is_bilingual

Primary label: `trust` (test/public-result expectation review; no incorrect mathematics demonstrated).

Repair ownership: local Rust test/expectation work after confirming the public contract. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn new_rule_normal_output_is_bilingual() {
    for (source, en, zh) in [
        (
            "have k Z\ntan(pi+2*k*pi)=0",
            "Exact periodic trigonometric value",
            "精确周期三角值",
        ),
        (
            "C_abs(3+4*i)=5",
            "Exact numeric complex modulus",
            "数字复数模长精确计算",
        ),
        ("3^(-2)=1/9", "Exact rational calculation", "精确有理数计算"),
        ("finite_set_max({1/3,1/2})=1/2", "Exact finite-set maximum", "有限集合最大值精确选取"),
        ("pi/4<pi/2", "Exact pi coefficient order", "pi 系数精确比较"),
        ("e>1", "Euler constant exceeds one", "自然常数 e 大于一"),
    ] {
        for (language, expected) in [(OutputLanguage::English, en), (OutputLanguage::Chinese, zh)] {
            let mut runtime = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            });
            let result = runtime.run_litex_code(source).unwrap();
            assert!(result.success);
            assert!(emit_run_normal(&result, &runtime, "eval", None).contains(expected));
        }
    }
}
```

Observed failure excerpt:

```text
thread 'execute::exact_numeric_periodic_modulus::new_rule_normal_output_is_bilingual' (71852202) panicked at src/execute/../../tests/unit/execute/exact_numeric_periodic_modulus/tests.rs:246:13:
assertion failed: emit_run_normal(&result, &runtime, "eval", None).contains(expected)
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::exact_numeric_periodic_modulus::new_rule_normal_output_is_bilingual -- --exact --nocapture
```

## logarithm_algebra_for_positive_nonunit_bases

Primary label: `trust` (test/public-result expectation review; no incorrect mathematics demonstrated).

Repair ownership: local Rust test/expectation work after confirming the public contract. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn logarithm_algebra_for_positive_nonunit_bases() {
    for source in [
        "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,1/2)=1", "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,1)=0",
        "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,(1/2)^(-3))=-3",
        "1/2 $in R\n1/2>0\n1/2!=1\n(1/2)^(-3)=8\nlog(1/2,8)=log(1/2,(1/2)^(-3))=-3",
        "e $in R\ne>1\ne!=1\ne>0\nlog(e,e)=1",
        "1 $in R\nforall b R:\n    b>0\n    b!=1\n    =>:\n        log(b,b)=1\n        log(b,1)=0",
        "1 $in R\nforall b R:\n    0<b\n    b!=1\n    =>:\n        log(b,b^(-3))=-3",
    ] { check(&format!("0 $in R\n{source}"), true); }
    for source in [
        "log(1,1)=1", "log(0,1)=0", "log(-2,-2)=1",
        "log(1/2,8)=3", "log(1/2,2)<log(1/2,4)", "e<1",
        "forall b R:\n    b>0\n    =>:\n        log(b,b)=1",
    ] { check(source, false); }
    let json = check("0 $in R\n1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,(1/2)^(-3))=-3", true);
    assert!(json.contains("LogOfPowerSameBase") && json.contains("proof_of_requirement_facts"), "{json}");
    let json = check("0 $in R\ne $in R\ne>1\ne!=1\ne>0\nlog(e,e)=1", true);
    assert!(json.contains("NativeEulerGreaterOne") && json.contains("LogBaseSelf"), "{json}");
}
```

Observed failure excerpt:

```text
thread 'execute::exact_numeric_periodic_modulus::logarithm_algebra_for_positive_nonunit_bases' (71852186) panicked at src/execute/../../tests/unit/execute/exact_numeric_periodic_modulus/tests.rs:390:5:
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "kind": "fact",
      "statement": "0 $in R",
      "verify": {
        "type": "atomic_except_equality",
        "success": true,
        "fact": "0 $in R",
        "well_defined": {
          "well_defined_of_each_parameter": [
            {
              "type": "by_def",
              "family": "Literal",
              "kind": "Number",
              "obj": "0"
            },
            {
              "type": "by_def",
              "family": "StandardSet",
              "kind": "StandardSet",
              "obj": "R"
            }
          ],
          "predicate_signature": {
            "type": "builtin"
          },
          "predicate_domain": []
        },
        "searched_proof": {
          "type": "by_closed_calculation",
          "kind": "in",
          "value": {
            "representation": "decimal",
            "normal": "0"
          },
          "set": "R"
        }
      },
      "store_and_infer": {
        "stores": [
          {
            "fact_id": "f1",
            "fact": "0 $in R"
          }
        ],
        "infers": []
      }
    },
    {
      "success": true,
      "kind": "fact",
      "statement": "1 / 2 $in R",
      "verify": {
        "type": "atomic_except_equality",
        "success": true,
        "fact": "1 / 2 $in R",
        "well_defined": {
          "well_defined_of_each_parameter": [
            {
              "type": "by_def",
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::exact_numeric_periodic_modulus::logarithm_algebra_for_positive_nonunit_bases -- --exact --nocapture
```

