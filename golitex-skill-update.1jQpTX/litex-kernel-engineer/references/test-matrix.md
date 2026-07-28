# Test Matrix

Use the smallest relevant command first, then broaden.

- Build once with `cargo build --release`; never use `target/debug/litex` or
  default-profile `cargo test` for this workflow.
- One standalone scratch Litex example: first run
  `target/release/litex -compact -isolated -f examples/tmp.lit`; use
  `cargo test --release run_tmp0 -- --nocapture` only when its Rust harness is
  also required.
- Registered project file: use `target/release/litex -compact -f <file.lit>`;
  this executes the ordered manifest prefix through that file.
- Examples harness: `cargo test --release run_examples -- --nocapture`.
- Mechanics draft chapters and their project runner:
  `cargo test --release run_mechanics_textbook_chapters -- --nocapture`.
- MATH500 local snippets:
  `cargo test --release run_math500_litex_simple -- --nocapture`.
- Whole-project gate: `target/release/litex -compact -r <module>`. Use it only
  for an explicit complete-module/final check, not for a one-file change.
- Kernel/parser/runtime/verifier/builtin/infer/well-definedness/output changes:
  `cargo test --release run_all -- --nocapture`.

Do not report bare `cargo test` timing as user-facing Litex performance: its
default profile is unoptimized. If output is strange or misleading, report it
as a diagnostics issue even when the proof succeeds.
