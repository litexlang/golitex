# CodeSource

`CodeSource` carries the path and publication identity of code in one value.
`Runtime.current_file` is the authoritative source for new input. Token blocks,
AST `SourceLine.origin`, parse errors and file-environment snapshots use that
same type. AST locations copy their token block's source instead of reading a
second live source argument.

Before the consolidation, opening an export required two independent updates:

```rust
// runtime.set_code_source(CodeSource::RootExport { export_file_id });
// runtime.begin_source(RealOrVirtualPath::Real(path));
```

The current interface opens it with one source value:

```rust
runtime.begin_source(CodeSource::RootExport { path, export_file_id });
```

`Eval`, `Repl` and `Real(PathBuf)` keep file-root symbols plain. `RootExport`
adds an export file ID; `ImportedExport` adds both a global module ID and an
export file ID. Both export variants also carry the real path used in errors.
The file runner derives its path and module context from the source instead
of accepting those as additional arguments.

A continued `-session` changes `runtime.current_file` to `CodeSource::Repl`
without opening a new environment or clearing accepted bindings. Its new
token blocks, AST locations and errors refer to `<repl>`. Previously parsed
locations and the file environment's entry snapshot keep their original source.
Soft statement failure still preserves earlier successful statements.

The CLI regression starts a standalone file containing:

```litex
have k N
k >= 0
```

It then enters `k >= 0`, the rejected `1 = 2`, and `k >= 0` again in the same
session. Both references to `k` succeed; the false equality remains rejected.
Malformed interactive input is separately checked for standalone, registered
and extra-file sessions: it reports `<repl>` while the final batch envelope
retains the original file path and results.

Boundary found during verification: a registered export with `have k N` can
fail `k >= 0` in the continued REPL. Its stored occurrence is export-qualified,
while a new REPL occurrence is plain. Both source variants retain those
pre-existing qualification rules in this refactor. The unresolved symbol
identity transition is tracked in `src/runtime/todo.md`; source consolidation
does not establish that exported bindings are reusable as plain REPL facts.

Knowledge-base ABI 9 serializes the source path with its IDs. Older caches
fall back to a source build. Warm imports remap source module IDs together
with symbol references and construct the environment snapshot using the current
configured export path. Existing path-keyed cache matching remains unchanged:
a moved module rebuilds its cache rather than reusing a stale path. Non-UTF-8
source paths are not encoded lossily; the optional cache write is skipped.

Focused verification:

```sh
cargo test --release --lib code_source_tests
cargo test --release --lib mount_remaps_imported_source_identity_and_preserves_its_path
cargo test --release --lib run_project_kb_cache_write_then_hit_cross_mod
cargo test --release --test cli_feedback file_session
```

The full Rust/CLI kernel gate is `cargo test --release`. The acceptance run
uses `CARGO_TARGET_DIR=tmp/2026-10-09/unify-code-source/target` to avoid
contention with unrelated builds in the shared target directory. The refactor
does not change Litex syntax, proof rules, symbol qualification or statement
transactions.

Acceptance results on 2026-10-09:

- Release build, the three focused source tests, source-ID remapping, cold/warm
  imports and all seven source-bearing JSON goldens passed.
- The standalone release CLI passed its clean file gate. Both `k >= 0`
  assertions survived the intervening rejected `1 = 2`; malformed interactive
  input reported `<repl>`.
- All 27 CLI/integration tests passed. The binary and Rust documentation gates
  also passed (both contain zero tests).
- The full library gate ran 1360 tests: 1354 passed and six Lean compiler tests
  failed. This is **not** a passing full-kernel result. The source/KB/runtime
  suites passed. The failing compiler does not consume `CodeSource`,
  `Runtime.current_file` or `SourceLine.origin`; no pre-change executable test
  baseline was available because the initial working tree did not compile.

The six failures are in `src/compile_to_lean/tests.rs`:

```text
phase2_all_verified_problem_profiles_emit_replayed_artifacts
phase2_computed_value_equality_replays_the_selected_subterm_rewrite
phase2_half_substitution_rejects_deleted_duplicate_wrong_and_unused_citations
phase2_two_closed_aliases_preserve_source_substitution_order
phase2_typed_half_uses_the_actual_closed_substitution_and_closed_child
simplification_alias_equality_uses_its_stored_id_in_the_selected_rewrite
```

For example, Litex accepts `let half = 1 / 2` followed by `half + half = 1`,
but Lean emission reports `WD/Producer: No preceding original constructor or
certified parameter supplies this object.` These failures remain outside the
source consolidation. One obsolete compiler-test field access was changed to
`cite_fact_id()` to restore test compilation; the compiler implementation was
not repaired by this task.
