# Litex REPL Try Workflow

Build once with `cargo build --release`, then use one persistent
`target/release/litex -compact -session -before <current-file.lit>` process
for iterative proof debugging of a registered file.
Never use the debug binary for this workflow.

`-before` executes the ordered project prefix strictly before the target,
skips the target's current contents and everything after it, and accepts source
fragments in the target file's environment. The same loop applies when the
target is empty, partial, or failing.

Recommended loop:

1. Start release `-session -before <current-file.lit>` once and wait for
   `{"event":"ready","mode":"project"}`.
2. Send the target's first top-level statement as literal Litex wrapped in one
   outermost `try:` session frame.
3. If it succeeds, write the accepted statement to disk without the wrapper
   and send the next source statement.
4. If it fails, keep the same process and send only the corrected current
   statement in another outermost `try:`.
5. If a real blocker is identified, keep the intended statement, use the
   narrowest legal `trust`, record the debt, and continue.
6. After all accepted code is on disk, run release `-f <current-file.lit>` as
   the clean file checkpoint.

For example, when `chap5.lit` follows `chap4.lit`, start
`-session -before chap5.lit`. A successful chap5 frame commits into the live
Runtime. A failed outermost `try:` normally rolls back only that frame,
preserving chap1--chap4 and every earlier successful chap5 frame. Restart only
if the process exits or cannot accept another frame, the registered prefix
changes, or an already committed declaration must be replaced; then replay
chap5 from its first statement.

Example candidate:

```litex
try:
    claim:
        ? forall x R:
            x = x
    forall x R:
        x = x
```

Guidelines:

- Use direct Litex `try:` as the transaction boundary.
- A failed `try:` should not leak facts into the parent environment.
- Do not use Python-side `sandbox_run()` as the primary workflow when direct
  Litex `try:` is available.
- Do not rerun `target/release/litex -compact -f long_file.lit` for every small
  candidate proof edit. Use project-aware `-f` only for file baseline,
  checkpoint, and final file verification. Use release `-r` only for an
  explicit complete-module gate.
- Optionally use
  `target/release/litex -compact -f <current-file.lit> -trust-before-line <X>`
  for a disk-first suffix preview. `X` must be the exact physical top-level
  statement header of the first changed or not-cleanly-verified statement.
  Statements before `X` skip well-definedness and proof verification; a suffix
  that depends on them is `indirect_trust`, so this run is never `checkable`.
  Move `X` backward after any earlier edit and always finish with clean `-f`.
- Never use default-profile `cargo test` as the Litex verifier. Use the release
  CLI; use `cargo test --release` only when a Rust-only harness is required.
- Remember that `try:` is transactional, not an optimizer: it saves time by
  preserving an already-loaded context after failure.
- When evaluating speed, include failure-heavy trials; the benefit is largest
  when many candidate fragments are wrong before the final one verifies.
