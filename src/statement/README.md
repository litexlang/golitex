# Statement model

This directory owns the parsed statement data model. Parsing constructs these types; execution and verification consume them.

## Start here

| Path | Responsibility |
| --- | --- |
| [`statement.rs`](statement.rs) | Top-level `Stmt`, `ByStmt`, command, proof-block, and definition categories. |
| [`conversions.rs`](conversions.rs) | Conversions from concrete statement forms into the top-level enums. |
| [`definitions/`](definitions) | Axioms, algorithms, parameters, object/proposition definitions, strategies, structs, and theorems. |
| [`proof_blocks/`](proof_blocks) | Claims, examples, sketches, trusted statements, try blocks, and witnesses. |
| [`commands/`](commands) | Evaluation and tooling commands. |
| [`proof_directives/`](proof_directives) | `by ...` proof-selection and theorem-release statement forms. |

`mod.rs` contains only module wiring. Historical Rust module names remain as compatibility re-exports for one version.
