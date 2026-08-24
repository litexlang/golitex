# Statement model

This directory owns the parsed statement data model. Parsing constructs these types; execution and verification consume them.

## Start here

| Path | Responsibility |
| --- | --- |
| [`core/types.rs`](core/types.rs) | Top-level `Stmt`, `ByStmt`, command, proof-block, and definition categories. |
| [`core/conversions.rs`](core/conversions.rs) | Conversions from concrete statement forms into the top-level enums. |
| [`definitions/`](definitions) | Axioms, algorithms, parameters, object/proposition definitions, strategies, structs, and theorems. |
| [`proof_blocks/`](proof_blocks) | Claims, examples, sketches, trusted statements, try blocks, and witnesses. |
| [`commands/`](commands) | Evaluation and tooling commands. |
| [`by_stmt/`](by_stmt) | Explicit proof-method statement forms. |

`mod.rs` deliberately preserves the historical public Rust module names with explicit `#[path]` declarations. The physical grouping is therefore an ownership map, not an API migration.
