# Removing the runtime `entry` concept

## Before

The runtime had two overlapping ways to describe the selected execution target:

- `RunTargetKind` already distinguished code, file, and repository targets.
- Output wrappers additionally synthesized a printable `target.label`, including the historical value `entry`.

The module system also duplicated root identity in `ModuleManager.entry_module_id` and
`ModuleManager.entry_path_rc`, even though `ModuleId::ROOT` and the root
`ModuleRunner.main_file_path` already carried the same information. Source rendering could
therefore replace concrete virtual paths such as the old eval and REPL markers with the
synthetic source name `entry`.

## Now

- Requested batch execution is owned by the typed `RunTarget`; `RunTargetKind` is derived only
  when an output renderer needs the stable JSON kind.
- Compact target JSON contains only `kind`; detailed file and repository JSON may additionally
  contain the real `path`. There is no target display label.
- Root module identity is derived from `ModuleId::ROOT`; its path is read from the root module.
- Synthetic interactive sources use the target-derived labels `eval`, `repl`, and `session`.
- The public contract versions are runner `0.2`, result graph `3`, fact graph `0.2`, and
  definition graph `0.3`.
- Release and predeploy consumers validate runner `0.2`.

This is intentionally a breaking public API/schema change. No compatibility field, method, or
alias preserves the removed runtime concept.

## Boundary

Ordinary uses of the English word “entry” for map entries, configuration records, collection
items, or mathematical objects remain valid and are outside this change. Verifier semantics,
proof search, Litex-to-Lean translation, Lean sources, and textbook mathematics are unchanged.

The noncanonical top-level textbook mirror is not an owning source for this runtime contract;
the canonical textbook workspace under `scripts/` was included in the semantic scan.

## Evidence

- `cargo check --release` passed after the migration.
- `cargo test --release runner::target_execution::tests -- --nocapture`: 11 passed.
- `target/release/litex -compact -runner -e '1 = 1'`: exit 0, runner `0.2`, target
  `{"kind":"code"}` with no label or path.
- `target/release/litex -compact -graph -e '1 = 1'`: exit 0, result graph `3`, target
  `{"kind":"code"}` with no label or path.
- `python3 tests/tooling/test_predeploy_gate.py`: 12 passed.
- `python3 .github/scripts/release/test_preflight.py`: 6 passed.
- `cargo fmt -- --check` and `git diff --check` passed during the migration.
- Scoped semantic scans found no production use of the retired module fields, constructors,
  target label, source kind, or synthetic source value. The only literal runtime-shaped uses of
  `entry` are negative regression assertions.

Pending before final acceptance: rerun the focused graph/session/source/root tests,
`cargo build --release`, and `cargo test --release --lib` after unrelated concurrent ToLean edits
restore a compilable worktree.
