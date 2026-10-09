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
let ((statement, outcome), temporary_scopes) =
    self.run_in_temporary_parse_scopes_and_take_scopes(|runtime| {
        let stmt = runtime.parse_token_block(block)?;
        let statement = stmt.readable_string();
        let outcome = runtime.exec_stmt(&stmt)?;
        Ok((statement, outcome))
    })?;

if outcome.is_failed() {
    return Ok((statement, outcome));
}
self.parse_scope_stack = temporary_scopes;
Ok((statement, outcome))
```

The shared helper always restores the original scopes after the closure
returns. An error discards the temporary scopes; an `Ok` returns them for the
caller to commit. The runner drops them on soft failure and assigns them back
only after successful execution. The helper copies the existing layers at
their existing depth rather than pushing another lexical scope: scope 0 must
remain the file root for export qualification. It does not restore global IDs,
since failed ASTs/results may already contain them.

`Runtime::parse` uses the same helper and remains a parse-only batch API, with
whole-batch rollback on a parse error and explicit commit on success. The
source runner owns the longer parse-and-execution transaction.
A later parse/execution error preserves successful earlier blocks and their
reported results. Tokenization still happens for the entire source first;
tokenizer errors prevent all execution. Complete claim/thm/sketch proof bodies
are parsed before any nested execution.

## Acceptance

```bash
cargo test --release --lib binding_lifecycle_tests -- --nocapture
cargo test --release --lib function_signature_scope_tests -- --nocapture
target/release/litex -lang en -strict -f examples/stmt_nodes/definition/parse_scope_transaction.lit
```

The 12 strict regressions cover same-session correction, same-input correction,
failed obtain followed by `obtain k from exist k`, public parse rollback of
the whole scope stack, successful prefixes, rejection of references to failed
definitions, soft-failure continuation, hard-error ordering, nested proof
atomicity, monotonic IDs, root/import qualification, and tokenizer boundaries.
The same-source and REPL correction were also checked with the release CLI.
Eight related statement fixtures and both `identifier_resolution` and
`obtain_bindings` registered modules pass with exit 0 and JSON `success: true`.

The 2026-10-09 helper extraction preserves these behaviors: the 12 binding
lifecycle regressions and 6 function-signature scope regressions pass in the
release test executable. The strict release CLI tracer exits 0 with
`kind: run`, `success: true`, and `session_error: null`. The refactor moves
restoration into the shared helper while leaving explicit commit decisions
at the two entrypoints; it adds no public syntax or verification capability.

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
