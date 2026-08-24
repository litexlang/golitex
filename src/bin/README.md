# Standalone maintenance binaries

`cargo run --release --bin stmt_result_to_lean_compiler -- check lean/examples`
re-executes every paired `.lit` example, compares the generated Lean source
with the checked-in `.lean` file, and asks the Lean kernel to check each pair.

## Examples and boundaries

| Command | Behavior |
| --- | --- |
| `stmt_result_to_lean_compiler compile example.lit` | Writes the paired `example.lean` file. |
| `stmt_result_to_lean_compiler generate lean/examples` | Regenerates every checked-in example pair in sorted source-path order. |
| `stmt_result_to_lean_compiler check lean/examples` | Rejects generated-source drift or any Lean kernel failure without modifying the pairs. |

[`stmt_result_to_lean_compiler.rs`](stmt_result_to_lean_compiler.rs) owns only
these maintenance commands. The recursive Result consumer and its compiler
environment stack remain in
[`../stmt_result_to_lean_compiler/`](../stmt_result_to_lean_compiler/README.md),
and the ordinary `litex` command-line interface remains in
[`../cli/`](../cli/README.md).
