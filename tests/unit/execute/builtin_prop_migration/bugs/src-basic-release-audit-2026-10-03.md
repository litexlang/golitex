# src basic audit: tests/unit/execute/builtin_prop_migration/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## builtin_choice_definition_reuses_checked_pointwise_source

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn builtin_choice_definition_reuses_checked_pointwise_source() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have fn g_choice(alpha {1}) power_set({1}) = {1}\nhave fn f_choice(alpha {1}) {1} = 1\nforall alpha {1}:\n    f_choice(alpha) $in g_choice(alpha)\n").unwrap();
    assert!(run.success);
    let tokens = Tokenizer::new().tokenize("$is_choice_function_for({1}, power_set({1}), g_choice, f_choice)", rt.current_file.clone()).unwrap();
    let goal = rt.parse(&tokens).unwrap().remove(0);
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::IsChoiceFunctionForFact(goal))) = goal else { panic!("choice fact"); };
    let requirements = rt.choice_definition_requirements(&goal).unwrap();
    for requirement in requirements {
        let proof = rt.verify_fact(&requirement, VerifyState::top_level()).unwrap();
        if proof.is_failed() {
            let result = ExecStmtResult::Fact(ExecFactStmtResult::Failed(proof));
            panic!("{}\n{}", requirement.ir(), crate::json_output::project_stmt_detailed(&result, &rt).stringify());
        }
    }
    let fact = AtomicFact::IsChoiceFunctionForFact(goal);
    let proof = rt.verify_fact(&Fact::AtomicFact(fact), VerifyState::top_level()).unwrap();
    if proof.is_failed() {
        let result = ExecStmtResult::Fact(ExecFactStmtResult::Failed(proof));
        panic!("choice predicate\n{}", crate::json_output::project_stmt_detailed(&result, &rt).stringify());
    }
    let run = rt.run_litex_code("by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)\n").unwrap();
    assert!(run.success, "{}", crate::json_output::emit_run_detailed(&run, &rt, "test", None));
}
```

Observed failure excerpt:

```text
thread 'execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::builtin_prop_definition::builtin_prop_migration_tests::builtin_choice_definition_reuses_checked_pointwise_source' (71852545) panicked at src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/../../../../../tests/unit/execute/builtin_prop_migration/tests.rs:33:9:
choice predicate
{"success":false,"kind":"fact","statement":"<wd_failed>","verify":{"type":"atomic_except_equality","success":false,"phase":"well_defined","failure":{"phase":"predicate_domain","completed_requirements":[{"requirement":"$is_set({1})","verify":{"type":"atomic_except_equality","success":true,"fact":"$is_set({1})","well_defined":{"well_defined_of_each_parameter":[{"type":"by_def","family":"SetFormer","kind":"ListSet","obj":"{1}","child_obj_well_defined":[{"type":"by_def","family":"Literal","kind":"Number","obj":"1"}],"requirement_fact_verified":[]}],"predicate_signature":{"type":"builtin"},"predicate_domain":[]},"searched_proof":{"type":"builtin_rule","family":"IsSetFact","rule":"AlwaysTrue"}}},{"requirement":"$is_set(power_set({1}))","verify":{"type":"atomic_except_equality","success":true,"fact":"$is_set(power_set({1}))","well_defined":{"well_defined_of_each_parameter":[{"type":"by_def","family":"SetOperator","kind":"PowerSet","obj":"power_set({1})","child_obj_well_defined":[{"type":"by_def","family":"SetFormer","kind":"ListSet","obj":"{1}","child_obj_well_defined":[{"type":"by_def","family":"Literal","kind":"Number","obj":"1"}],"requirement_fact_verified":[]}],"requirement_fact_verified":[]}],"predicate_signature":{"type":"builtin"},"predicate_domain":[]},"searched_proof":{"type":"builtin_rule","family":"IsSetFact","rule":"AlwaysTrue"}}},{"requirement":"g_choice $in fn (__param_9 {1}) p
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::builtin_prop_definition::builtin_prop_migration_tests::builtin_choice_definition_reuses_checked_pointwise_source -- --exact --nocapture
```

