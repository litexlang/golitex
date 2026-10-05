# CLI / JSON low-level sweep — 2026-10-05

The reproduced CLI, session-output and JSON-codec defects below are repaired.
The release build, 158 focused Rust/CLI tests and 378 statement checks pass.
Proof rules, strict trust/axiom policy, AST shapes, Runtime/Env state and
finish/abort/transaction order are unchanged. JSON snapshots are presentation
data captured before the existing environment teardown.

## Before / after evidence

| Input / trigger | Observed before | Verified after |
| --- | --- | --- |
| `-strict -session -e` with the initial proof below, then REPL `have` | Failed eval JSON discarded the initial results | Retains all initial statement results and appends the hard session error; exit 1, empty stderr |
| `have k N; k >= 0`, then a session error | Re-rendering after abort lost `cite: "0 <= k"` | The pre-REPL snapshot preserves the complete results, including stores, infers and citations |
| `-f main.lit` with directory-local `litex.config` and the same source | Re-rendering after finish also lost object stores/infers and the citation | Export-file JSON is captured before finish/abort; callers preserve it and keep the original CLI operand in `path` |
| Bare REPL input `have` or one unclosed `"` | The same parse error printed twice | One stderr diagnostic, exit 1 |
| Continued REPL `have`, unclosed `"`, `$is_finite_set(1, 2)`, `$fn_eq(1, 2)` | Diagnostics named `<eval>` or the initial file | Interactive diagnostics name `<repl>`; file ownership and scope identity stay unchanged |
| `-extractpython -f missing.lit` and C / repository equivalents | Failed artifact lost command metadata | Success/failure share `format`, `target`, `path`, `output_path`, `language`; failure has null content and an extraction error |
| `-lang zh -extractpython 'have a R = 1'` | Extraction ignored the selected JSON language | Artifact and nested error keys follow the selected locale; both extractors cover all ten locales |
| argv bytes `-e`, `0xff` | Rust argument decoding panicked, exit 101 | One UTF-8 launch diagnostic, exit 2, empty stdout |
| Close stdout's reader before `-e '1 = 1'` / `-e '1 = 2'` | Broken pipe panic, exit 101 | No panic or stderr noise; original success/failure exit 0/1 survives |
| Detailed run projection of the initial theorem / its call | `statement` was absent or reconstructed incompletely | Normal, Compact and Detailed retain the same complete parsed statement; all ten locales and soft/hard failures are covered |
| JSON strings `"\b\f"`, `"\ud83d\ude00"` | Valid escapes rejected | Decode to the control characters / emoji; compact and pretty forms round-trip |
| Raw U+0001 in a JSON string; VT/FF outside strings | Invalid JSON accepted | Reject unescaped U+0000–U+001F and non-JSON whitespace; malformed/unpaired surrogates also reject |
| JSON `1e400` | Became infinity | Explicit finite-range error |
| `JsonValue::parse("1e20").as_u64()`; stringify of 2^64 | Saturated/emitted `18446744073709551615` | Overflow conversion rejects; serialization preserves the float instead of saturating |
| `-help` | Omitted both supported `-extract… -r <repository>` forms | Both forms and every note are present; usage/notes no longer rely on numeric indexes |
| `src/run_module/README.md` fixture link | `../../../examples/module_manager/` pointed outside the Git root | `../../examples/module_manager/` resolves to the actual fixtures |

Initial proof used in the session/full-prefix comparisons:

```litex
thm identity:
    ? forall x R:
        x = x
have k N
k >= 0
```

The REPL can still apply `by thm identity(2) => 2 = 2`. File tests cover no
config, a registered export target, and an unregistered target after exports,
including clean session exit and hard errors. They compare complete
`statement_results`, not just statement names. `-session` still mixes English
REPL text and final JSON; `-lang` controls JSON keys/explanations.

The JSON numeric representation remains `f64`. The u64 check uses an exclusive
2^64 boundary because `u64::MAX as f64` rounds up; the largest exactly
representable integer below that boundary remains accepted. This change adds
range validation, without changing the cache schema or introducing an
arbitrary-precision number model.

## Acceptance

All of these commands exited 0:

```sh
cargo test --release --offline --lib json_output::
cargo test --release --offline --lib knowledge_base::unit_tests
cargo test --release --offline --lib launch_command_tests
cargo test --release --offline --lib binding_lifecycle_tests
cargo test --release --offline --lib internal_error
cargo test --release --offline --lib error_forwarding_tests
cargo test --release --offline --test cli_feedback
cargo build --release --offline
python3 examples/test_statements/run.py --binary target/release/litex --require-no-gaps
target/release/litex -strict -f examples/stmt_nodes/definition/def_thm.lit
target/release/litex -strict -f examples/stmt_nodes/command/eval_store_result.lit
```

- Focused tests: **76 + 42 + 11 + 12 + 3 + 1 + 13 = 158 passed**.
  The 42 knowledge-base tests include six JSON-codec boundary/round-trip tests
  and the existing definition/storage/mount checks.
- Statement suite: **50 leaves, 378 checks, zero unexpected failures/gaps**.
- Both canonical examples: exit 0, successful run, null session error,
  empty stderr.
- The final release binary was also checked with Python's independent JSON
  parser for localized extraction success, extraction I/O failure, localized
  tokenization failure and a session error retaining the original citation.
  Native probes rechecked non-UTF-8 argv and closed-pipe exit 0/1.
- Scoped `git diff --check` passed. Task-created probe files and the completed
  SOP ledger were removed. Unrelated concurrent workspace changes were left
  intact. A whole-repository/kernel audit was outside this CLI/output sweep.

## Intermediate failures retained

The first JSON run passed 75/76 tests: the new Arabic `format` translation
collided with existing `form`. The same static collision check found Japanese
and Korean collisions. The new format translations were made distinct; the
existing collision test subsequently passed for all ten languages.

The first complete file-prefix comparison passed 12/13 CLI tests and failed
because ordinary registered-file output had already lost stores/infers and
citations after finish. Capturing at `run_export_file` and retaining the
snapshot fixed this earlier producer boundary. The full comparison stayed in
the regression test, and the final 13/13 CLI run passed.

Final release binary SHA-256:
`f98f3a1aae0f408e310ec1ad5e44705e969d4a8966c4d507879d21b68b3c894d`.
The 29 touched implementation/test/document paths' sorted path/content bundle
SHA-256:
`8dfa2a4b88dc8b2d7af14a8ef7d10591903fdb5ebc1b756707edf4dd5c84ae25`.
