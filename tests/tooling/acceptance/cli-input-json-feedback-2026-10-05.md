# CLI input and JSON feedback — 2026-10-05

The five requested changes are implemented and verified with the release binary.
Proof rules, trust policy, AST structs, Runtime/Env state and transaction semantics
are unchanged. Statement text is presentation metadata on `RunLitexCodeResult`.

## Verified behavior

1. `litex -extractpython '-2 < 0'` and its C equivalent previously failed at
   launch; both now accept the complete verified source (exit 0, artifact
   `success: true`). Source operands spelling `-strict` reach the source parser
   rather than enabling a flag. `-f` / `-r` operands may also start with `-`.
   Extraction's immediate `-f` / `-r` still select input mode; a missing path
   remains a launch error with exit 2. Empty operands and surplus tokens reject.

2. This unchanged input now retains complete declarations and calls in run JSON:

   ```litex
   thm identity:
       ? forall x R:
           x = x
   by thm identity(2) => 2 = 2
   release thm identity(3)
   ```

   Previously `statement` was the stored forall fact / `by thm identity`.
   Normal and Compact run JSON now show the complete parsed readable statement;
   `stores` still contain published facts. Ordinary axioms retain their names
   and the explicit Axiom proof-method tag. Text remains aligned through soft
   failures, hard-stop prefixes, locales and registered/unregistered file sessions.

3. `1 / 0 = 0` previously displayed `<wd_failed>` or bare REPL `error`.
   Run JSON now keeps `statement: "1 / 0 = 0"`, with
   `why_failed.phase: "well_defined"` and the message
   `Could not prove that the statement is well-defined.` Chinese output says
   `未能证明该语句中的表达式有定义。` The existing detailed failure still exposes
   the unproved requirement `0 != 0`; failed statements publish no facts.
   All ten locales are covered. REPL soft failures print Normal JSON and keep
   accepting input. Source-free projections use `<well_defined_not_proven>`.

4. Both `litex -e 'have'` and a source consisting of one unclosed `"` now
   produce failed run JSON on stdout, exit 1 and non-null `session_error`.
   Recognized batch I/O errors likewise produce JSON; extraction errors use
   the artifact error envelope. Existing exit codes are preserved. Invalid
   launch shapes retain stderr text and exit 2. Runtime errors now use readable
   diagnostics instead of `Runtime(ParseError(...))` Debug wrappers.
   Interactive `-session` output remains a mixture of REPL text and run JSON.

5. `eval 1 + 1` still publishes the checked equality `1 + 1 = 2`; the following
   `2 = 1 + 1` succeeds via the stored equivalence class. The contradictory FAQ
   and statement-index descriptions were corrected. Eval semantics are unchanged.

## Acceptance

All commands below exited 0:

```sh
cargo build --release --offline
cargo test --release --offline --lib launch_command_tests
cargo test --release --offline --lib json_output::
cargo test --release --offline --lib binding_lifecycle_tests
cargo test --release --offline --lib internal_error
cargo test --release --offline --lib error_forwarding_tests
cargo test --release --offline --test cli_feedback
python3 examples/test_statements/run.py --binary target/release/litex --require-no-gaps
target/release/litex -strict -f examples/stmt_nodes/definition/def_thm.lit
target/release/litex -strict -f examples/stmt_nodes/command/eval_store_result.lit
```

- Focused Rust tests: 11 + 76 + 12 + 3 + 1 + 7 = **110 passed**.
- Statement suite: **50 leaves, 378 checks, zero unexpected failures/gaps**.
- Canonical theorem/eval tracers: exit 0, `success: true`, null `session_error`.
- Scoped `git diff --check` passed. No task-authored drafts remain; automated
  integration fixtures clean their own temporary directories. The full
  repository gate was outside this localized change.

Intermediate evidence is retained here: the first parser regression run had
10 passes and one failure because missing extraction mode paths fell through
to inline-source parsing. Explicitly reserving `-f` / `-r` restored that boundary.
The first statement-suite run had 374/378 matches: four strict-trust cases still
expected Debug wrappers. Their expectations now require the full readable
forbidden-trust diagnostic; rejection status, exit and empty results are unchanged.

Release binary SHA-256:
`d43a1d2c5364cceac925be67b8cf11a76b8e450e9a1cd7aca2ce2f7df3e880f0`.
The 20 implementation/test files' sorted path/content bundle SHA-256:
`d827ceaabd4a578088325957ceb0dd63b7828ab563537296e6b8f06cd5914587`.
Concurrent unrelated workspace changes were left intact.
