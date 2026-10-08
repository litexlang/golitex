# Unified Lean command acceptance

Previously, `main` intercepted `parse_lean_command`, stripped `-lean`, and
executed an ordinary `LaunchCommand::File` outside `run_command`.
Now the shared parser produces `LaunchCommand::CompileToLean`, the shared
dispatcher returns `RunCommandOutcome::CompileToLean`, and `run::output`
renders the artifact or phase diagnostic. Execution failures remain
`RuntimeResult::Err`; only a complete source artifact is a successful result.

The tracer is `lean/examples/one_equals_itself/statement.lit`. Its generated
source is byte-identical to the canonical `.lean`. Standalone-file provenance,
strict/language options, operand ownership, rejected command combinations,
verification/compilation failures with no partial stdout, and exit codes
are covered by the unit and real-binary tests.

Verified on 2026-10-08:

- `cargo test --release --lib run::`: 20 passed.
- `cargo test --release --test compile_to_lean_cli --test compile_to_latex_cli --test cli_feedback`: 25 passed.
- `target/release/litex -strict -lang en -f lean/examples/one_equals_itself/statement.lit`: exit 0, successful Normal envelope.
- `target/release/litex -strict -lean -f lean/examples/one_equals_itself/statement.lit`: exit 0, canonical source byte comparison passed.

The previously reported `phase1_known_forall_keeps_free_global_references_fixed`
test was removed at the maintainer's request on 2026-10-08. Its removal does
not establish support for the corresponding compilation capability.
Remaining compiler tests are rechecked separately from command-routing tests.
The command-routing acceptance above does not establish Lean-kernel acceptance.
