# Native finite coordinate spaces

Status: complete for the native coordinate-space increment, 2026-10-31.

## Contract and proof spine

- Construct `coordinate_space<K,F,n>` on exactly `finite_seq(K,n)`, for K nonempty, F an existing Field<K>, and every n in N, including zero.
- Reuse the existing `zero_coefficients`, `add_coefficients`, `neg_coefficients` and `smul_coefficients`; do not introduce duplicate operations or retarget a raw function-space record.
- Prove the VectorSpace laws pointwise using the supplied Field and function extensionality, then publish the actual record and its imported carrier theorem.
- Target: `std/algebra/finite_span.lit`. Durable imported tracer: this directory's `main.lit`, with real and complex coordinates, zero dimension and reuse of an existing generic vector-space theorem.
- Impact: L2 source-only; no native/AST/Env/Runtime changes, new assumptions or textbook edits. Broader package selection remains pending.

## Protocol

- Continue the current release Session loaded through finite_span, one statement per submission; retain the context after normal failures.
- Record attempts before materializing a coherent accepted source checkpoint. Clean source/imported gates belong at checkpoints and completion.
- Keep validation artifacts in this hidden std-owned directory, excluded by the existing std packaging rule. No files outside the authorized std source and experiments planning workspaces.

## Acceptance

- [x] Generic construction and carrier theorem accepted in Session.
- [x] Strict saved source and independent imported consumer accepted.
- [x] Zero dimension and native finite_seq compatibility demonstrated.
- [x] Refusal controls retain accepted Session context.
- [x] Source-owned documentation, evidence and scope audit complete.

## Completion evidence

Strict source: 43 accepted statements. Independent std-imported consumer: 39 accepted statements, including R/C computations, native matrix use, n=0 and generic theorem reuse. Three expected scalar/index/wrong-value refusals retain context. See gates.json and acceptance.json. No new assumptions, native changes or payload paths.

Concurrent builds replaced the shared release executable during the task. All three increments receive final revalidation with `LITEX_CHECK_BINARY` selecting the same task-owned snapshot. See binary_snapshot.json. The snapshot is temporary; normal checker invocations default to target/release/litex and reject binary changes during verification.
