# Parse bindings across statement execution

Before this repair, `run_litex_code` parsed every block before execution.
Parsing occupied declaration names even when `exec_stmt` subsequently discarded
the failed statement's temporary execution environment:

```litex
have k N = -1
have k N = 1
k = 1
```

Before: line 2 raised `already bound` before either declaration executed.
After: statement results are `[Failed, Success, Success]`, with no session
error. The overall run correctly remains unsuccessful because line 1 failed.
In an interactive session, the three submissions print `error`, `success`,
`success`, and the corrected definition remains usable.

The runner now uses one transaction per complete top-level `TokenBlock`:

```rust
let scopes_before = self.begin_parse_scope_transaction();
let result = self.parse_token_block(block)
    .and_then(|stmt| self.exec_stmt(&stmt));
```

Successful execution retains the installed parse scopes. Soft failure or a
parse/execution error restores `scopes_before`. The shared helper copies the
existing layers at their existing depth rather than pushing another lexical
scope: scope 0 must remain the file root for export qualification. It does not
restore global IDs, since failed ASTs/results may already contain them.

`Runtime::parse` remains a parse-only batch API, with whole-batch rollback on a
parse error. The source runner owns the longer parse-and-execution transaction.
A later parse/execution error preserves successful earlier blocks and their
reported results. Tokenization still happens for the entire source first;
tokenizer errors prevent all execution. Complete claim/thm/sketch proof bodies
are parsed before any nested execution.

## Acceptance

```bash
cargo test --release binding_lifecycle_tests -- --nocapture
target/release/litex -strict -f examples/stmt_nodes/definition/parse_scope_transaction.lit
```

The 12 strict regressions cover same-session correction, same-input correction,
failed obtain followed by `obtain k from exist k`, public parse rollback of
the whole scope stack, successful prefixes, rejection of references to failed
definitions, soft-failure continuation, hard-error ordering, nested proof
atomicity, monotonic IDs, root/import qualification, and tokenizer boundaries.
The same-source and REPL correction were also checked with the release CLI.
Eight related statement fixtures and both `identifier_resolution` and
`obtain_bindings` registered modules pass with exit 0 and JSON `success: true`.

## Broader gate evidence

The clean committed `f9ebb0935` comparison reports 347 passed / 6 failed.
Adding only this repair and its tests reports 359 passed / the same 6 failed,
at the same assertions. The pre-existing failures are:

- `not_in_and_set_algebra_builtin_rules`
- `template_have_fn_by_induc_object_definition_unfold`
- `order_stage_a_finite_set_size_union_and_surjection`
- `acceptance_cite_readable_no_hash_wrappers`
- `acceptance_hot_atomic_chinese_from_known_in_n`
- `normal_json_have_natural_then_nonnegative_by_builtin`

A frozen snapshot including the concurrent working-tree edits reports
354 passed / 6 failed before this repair and 366 passed / the same 6 failed
after it. An earlier live-tree run had two additional failures while the
concurrent order/power changes were still being completed; they pass in the
frozen comparison. Consult
`tmp/2026-10-01/identifier-repair/sequential-validation.json` and the paired
logs for the exact snapshots. No new failure appears in either controlled
before/after comparison. Disposable source/build copies were removed after
preserving the results and hashes.

The `run_examples` Cargo filter currently selects zero tests; direct release
CLI fixtures supply actual example coverage. The Markdown harness ran 177
fences with 176 passing. Its remaining failure is a concurrently added audit
fence containing only `by thm only_natural(-1) => -1 >= 0`, without the theorem
declaration from the preceding independent fence. This repair does not change
that audit document or its theorem-verification behavior.
