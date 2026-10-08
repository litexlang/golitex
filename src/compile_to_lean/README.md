# Litex-to-Lean Compiler Implementation

This module replays successful typed Litex execution results into Lean source.
Its implementation and internal design rationale are documented here. The
[compiler guide](../../docs/Litex_To_Lean_Compiler_Guide.md) owns the broader
design principles and source/generated example walkthroughs;
[CLI documentation](../../docs/cli.md#lean-compiler-boundary) owns invocation
and output behavior.

## Entry point and owners

```rust
pub fn compile_run(
    result: &RunLitexCodeResult,
    runtime: &Runtime,
    artifact_namespace: &str,
) -> Result<String, LeanCompileError>
```

| File | Responsibility |
| --- | --- |
| [compile_run.rs](compile_run.rs) | Validate the successful run, replay statements and evidence, and return the complete Lean source. |
| [lean_compile_error.rs](lean_compile_error.rs) | Report the source statement index, evidence route, and rejection reason. |
| [tests.rs](tests.rs) | Exercise supported replay and reject missing, changed, or out-of-scope evidence. |
| [mod.rs](mod.rs) | Declare the module and export its public API. |
| [../run/run_compile_to_lean.rs](../run/run_compile_to_lean.rs) | Parse the preview mode, verify standalone source once, and invoke this module while Runtime remains live. |
| [../../lean/Litex.lean](../../lean/Litex.lean) | Define object semantics, certified constructors, and proved native bridges used by emitted terms. |

`Runtime` is borrowed for citation resolution. It does not run a second proof
search for the compiler. Display strings and presentation JSON are not replay
inputs.

## Replay pipeline

`compile_run` rejects a failed or incomplete source run, then visits
`statement_results` in order. It returns the assembled artifact only after
every statement succeeds. `compile_statement` currently accepts successful
fact statements; other statement families have explicit unsupported branches.

For each fact, `compile_verify` dispatches on the successful `VerifyFactResult`
and its selected `searched_proof`. It replays object WD before the truth proof,
checks that the evidence subjects match the source objects/facts, validates
storage, and registers the emitted fact for later citations. Additional
inferred facts are not promoted to assumptions: citing an inference without
a supported replayed producer is rejected.

`compile_forall` pushes a `CompilerScope` carrying the result's captured local
environment, introduces binders and assumptions, replays the body, and pops
the scope on either success or error. Generic binders retain their host type,
`Litex.Representation`, certified `Litex.Obj`, and membership hypotheses.

## Internal representations

| Type | Role |
| --- | --- |
| `ObjectTerm` | Source object and its emitted certified Lean term, with optional numeric bridge evidence. |
| `NumericTerm` | Native numeric value, its denotation proof, and complex-membership proof. |
| `FactTerm` | Exact source fact, emitted proposition, and emitted proof. |
| `CompilerScope` | Active identifier, object, fact-ID, and WD-ID registries plus an optional captured environment. |

Identifier IDs preserve binder identity, FactIds preserve citations, and
WellDefinednessIds preserve cached construction dependencies. Object IR keys
locate certified terms; they do not authorize discovering a new proof from a
matching proposition. `resolve_fact` and `resolve_wd` resolve recorded subjects
from captured scope/Runtime context, while producer registries require the
corresponding evidence to have been replayed.

## Adapter design and rejection boundaries

Route-specific adapters consume the evidence variant selected by Litex.
Reflexivity emits `Litex.sameRefl`; closed numeric calculations validate their
exact endpoint certificates; rational normalization validates the supported
expression domain and ordered nonzero requirements before emitting a native
normalization proof through `Litex.NativeBridge`.

The rational adapter uses fixed `ring` or guarded `field_simp`/`ring` output.
The empty Rational tag contains no monomial trace: Lean checks the emitted
normalization proof itself. Do not describe this as replaying an unavailable
low-level normalization trace, or replace the selected route with a theorem
chosen by goal shape.

Arithmetic WD adapters preserve constructor shape and replay child WD and
domain evidence. Membership can attach numeric denotation evidence to an
existing object; it does not replace the object's generic host representation.
Unsupported constructors, statement families, routes, or unresolved producers
return `LeanCompileError` for the entire artifact.

## Extending and checking the module

Start with the actual producer result and its source-facing contract. Add an
adapter for that selected route, check exact subjects and ordered dependencies,
and use a proved semantic bridge. Preserve a real source/generated pair and
an executable rejected boundary. Result-contract gaps must be repaired at
their owning producer rather than reconstructed from presentation text.

Focused Rust tests can be run with:

```sh
cargo test --release --lib compile_to_lean::tests
```

These tests cover replay contracts; successful string generation alone does
not establish Lean kernel acceptance. The guide describes the separate source,
compiler, regeneration, and Lean checks. Canonical pairs live under
`lean/examples/`; fixtures, gate tools, receipts, and pinned Lean/Mathlib build
state belong to the local-only `scripts/litex_to_lean/` workspace. Keep generated
proofs compiler-owned and regenerate them through the actual CLI.
