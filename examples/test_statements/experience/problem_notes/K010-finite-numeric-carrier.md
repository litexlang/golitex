# K010: finite numeric carriers

Task: repair the user's finite enumeration example on 2026-10-02.
Scope: standard-set membership evidence, goal well-definedness, and finite enumeration in golitex.

The unchanged target now succeeds in strict mode:

```litex
by enumerate finite_set:
    ? forall n {0, 1}:
        n + 0 = n
```

Active fixture: [finite-numeric-enumeration.lit](../../boundaries/finite-numeric-enumeration.lit). Both assignments have their own binding assumptions and proved conclusion. The universal identity also succeeds without an equality choosing a particular value of n.

## Cause and repair

The enumerator correctly substituted each value, but first checked the universal goal's well-definedness. Its binder was known to belong to `{0, 1}`; membership search did not lift that finite carrier to a numerical standard set. The baseline target failed, while an explicit checked `{0, 1} $subset C` bridge made it pass: [baseline evidence](../../proof_journals/k004_k010_baseline.json).

The [membership builtin owner](../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/in_fact.rs) adds `FiniteSetSubsetMembership`. It verifies membership in a known displayed finite set, then verifies every listed member's membership in the requested standard carrier. Its dedicated certificate retains the source set, source membership proof (including known-fact citation and argument equality evidence), and every member proof. The [detailed projection](../../../../src/json_output/project_detailed/builtin_atomic_gen.rs) emits these actual premises; the [normal explanation](../../../../src/json_output/explain/atomic_builtin_rule/in_fact.rs) names the rule in English and Chinese.

Source membership uses existing evidence; member premises use the existing bounded builtin policy: known evidence, closed calculation, or the caller's permitted builtin leaf. Children cannot reopen builtin, deep, or rewrite search. This prevents `n in {n}` or cyclic membership alone from inventing a numerical type. The standard-set lift projection also retains its nested source proof, so finite evidence survives the route through a narrower numeric standard set. The enumerator's original goal-WD, assignment verification, and transactional scopes remain in force. No AST or execution-environment fields changed.

## Acceptance and controls

[Statement-boundary Rust tests](../../../../tests/unit/execute/statement_boundaries/tests.rs) check both enumeration interfaces, two proved assignments, nested proof JSON, symbolic arithmetic without choosing a value, symbolic real members, nonnumeric members, false conclusions, division by zero, and parameter-scope cleanup. Existing enumeration premise/body and rollback tests remain selected. A set-valued singleton cannot acquire a numeric type. The valid carrier `{0, 1}` cannot lift to `N+` merely because 1 is positive. A mixed numeric/set carrier remains rejected; its list-set WD cannot prove the distinctness condition, so this control alone is not evidence for the later member-type check.

```bash
cargo test --release --lib statement_boundary_tests
python3 examples/test_statements/run.py --leaf ByEnumerateFiniteSetStmt
python3 examples/test_statements/run.py --leaf ByForStmt
```

Original note/input/output: [prior records](../../proof_journals/k004_k010_d001_prior_records.json). Initial fresh CLI acceptance and rejection controls: [k010_first_acceptance.json](../../proof_journals/k010_first_acceptance.json). Final results, commands, and release hash: [focused acceptance](../../proof_journals/k004_k010_d001_acceptance.json).
