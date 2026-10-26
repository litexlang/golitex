# Explicit namespace aliases

The manifest declares `[alias] C = Library::defs` and `D = Library::other`.
`C::value` and `Library::defs::value` resolve to the same declaration. The
library deliberately lists `other` before `defs`, proving that aliases select
the named export rather than the only or first export.

`main.lit` covers objects, functions, props, theorem calls, templates and
struct carriers, without trust or axioms. It preserves the former source
forms as comments and keeps the current assertions active.

```sh
target/release/litex -lang en -strict -f examples/module_manager/namespace_aliases/main.lit
cargo test --release --lib namespace_alias -- --test-threads=1
cargo test --release --test installed_std_cli
```

The CLI gate requires exit 0 and Normal JSON with `kind: run`,
`run_result: "success"`, `session_terminated: false`, and `termination: null`.
Rust regressions execute removed `:::` forms in object, prop, theorem, release,
template and struct positions. They also reject duplicate aliases, collisions
with local exports, alias chains, unknown or unused targets, missing symbols,
plain alias names and attempts to re-export an alias as a file.

Aliases belong to the current manifest. A dependency may reuse the same alias
for a different target. They may share an import spelling, since only the
first part of a two-segment reference uses the namespace alias. Full
three-segment paths always resolve real imports and exports. The real cache
regression checks a cold import, actual warm skips, target-change invalidation,
and invalid-alias rejection before cache replay. The installed-std CLI tests
cover aliases in `-f`, `-r`, `-e`, bare REPL and continued file Sessions.

Compatibility: `:::` is removed and emits a migration diagnostic. Use the full
`Library::defs::name` path or configure an alias and use `C::name`. KB ABI 10
forces old cached imports to be checked again; it does not change stored
module/file identity or the definitions wire format.

## Validation receipt (2026-10-26)

The focused alias suite passed all 9 tests, and the rebuilt release CLI passed
both the strict file and project gates. All 143 migrated Litex inputs passed
their contracts: 21 positive files and 122 negative files, with each negative
still failing at its recorded final statement and original phase. The six
qualified-template CLI checks passed.

The full documentation runner executed 1020 fences; four unchanged snippets
failed: the named-object CoordinatePair fence in both compiler guides omits
its struct declaration, and the remainder-composition fence in both Manuals
fails at `a % 2 = (a % 8) % 2`. The exact fence bodies also occur in HEAD and
contain no qualified names. These are outside the namespace change.

The existing Stmt Python collector ran 393 checks. Every success/failure verdict
matched, but 143 metadata/sequence assertions failed: 96 still read the retired
`statement_results[].why_failed.phase` field instead of `errors[].phase`, and
47 expect the earlier hard-session/statement-sequence behavior. This collector
is not a green acceptance gate. The focused alias negatives inspect current
Normal JSON directly. No unrelated verifier or collector migration is included.

Rust coverage: `cargo test --release --locked --all-targets --no-fail-fast`
passed all 2855 unit tests and 82 integration tests inside the sandbox. Its
remaining five `reading_http` cases failed only because sandbox policy blocked
their 127.0.0.1 listener. The same compiled test target
`target/release/deps/reading_http-45c20257b387ce73` was then run outside the
sandbox and passed all five. Combined coverage is 2855 unit tests and 87
integration tests, with no remaining Rust test failure. Installed-std CLI tests
include aliases in eval, REPL and continued Sessions. No local textbook,
packaging, release or external Lean gate was run.
