# To-Lean IR MVP

To-Lean no longer re-reads a verified source statement and guesses a tactic
from its syntax. The verifier produces a backend-facing proof IR; the Lean
emitter accepts only that IR.

## Execution contract

`Runtime` has an explicit `to_lean_mode` flag.

- Every fact admitted by runtime storage to an environment's known-fact cache
  receives a runtime-unique `FactId`, in ordinary execution as well as compiler
  execution. Display, nested-binder, and alpha-normalized cache aliases for one
  stored fact share the same ID.
- Ordinary execution leaves `StmtResult::to_lean_ir()` as `None`.
- To-Lean mode attaches `Some(StmtToLeanIR)` only after successful statement
  execution. Fact IR is assembled after storage, so its citations can carry
  stable IDs rather than matching later by display text.
- Local proof assumptions are distinguished from trusted facts. When a local
  assumption was stored in a temporary environment, its ID survives in the
  returned proof IR and becomes a Lean name such as `h_f18`.

The environment cache deliberately stores only `FactId` plus the existing
source location. Proof trees, origins, inferred consequences, local/global Lean
names, and recursive dependencies live in statement results and To-Lean IR.

## Statement and proof IR

The MVP constructs four statement forms:

- `AbstractProp`
- `Prop`
- `Trust`
- `Fact`

A fact contains its proposition, optional stored `FactId`, and a recursive
`FactProofToLeanIR`. Proof routes are classified as trusted, local assumption,
known fact, known-forall instantiation, builtin rule/strategy, definition,
user strategy, composite proof, forall introduction, inference, statement memo,
or explicitly unsupported.

Known-forall evidence retains typed argument objects. Parameter-type checks are
kept separately from actual domain premises: Lean's binder type checks the
former, while the latter are passed as proof arguments. Statement memoization
is a transparent proof wrapper and does not erase the underlying route.
For forall introduction, the corresponding temporary parameter-typing facts
are likewise retained separately (with their IDs), even though the emitter
realizes them through typed Lean binders rather than local proposition names.
Cached citations and known-forall requirements capture their source `FactId`
while the source environment is alive, so a temporary premise can remain a
local Lean proof argument after its Litex scope has been popped.

## Lean surface

For a standalone file such as `chapter01-introduction.lit`, the generated Lean
surface begins with:

```lean
import Mathlib

universe uLitex

namespace chapter01_introduction

abbrev LitexSet := Type uLitex
abbrev LitexFact := Prop

-- generated declarations

end chapter01_introduction
```

`uLitex` is a Lean universe-level variable used only by the generated
representation; Litex itself does not expose a universe concept. The emitter
never uses a fixed synthetic namespace such as `LitexGenerated`. A registered
file or module uses its canonical Litex name, with `::` mapped to Lean's `.`, so
`A::chap2` becomes `A.chap2`. A standalone runtime whose source path ends in
`.lit` falls back to the sanitized file stem. The canonical name takes
precedence over that fallback.

`to_lean_from_source` remains anonymous and emits declarations at the file
root, even when its diagnostic label looks like a `.lit` path. The pure
`emit_lean_from_ir` boundary is likewise anonymous because IR intentionally
contains no source context. Callers compiling an actual file should use
`to_lean` with that file's Runtime context.

This namespace selection scopes one emitted source. It does not add repository
traversal, Lean imports, or cross-file `FactId` lowering to the current MVP.

The current lowering is intentionally small:

- `abstract_prop` becomes a polymorphic `opaque` proposition;
- a typed `prop` over the currently supported `R`/set parameter surface becomes
  `def` (or `opaque` when it has no body);
- only an explicit Litex `trust` becomes Lean `axiom`;
- stored proved facts become `theorem litex_fact_<id>`;
- known-forall application uses the cited `FactId` directly;
- definition evidence uses the named Lean definition;
- forall introduction creates local hypotheses named from temporary FactIds;
- verified rational-expression normalization is discharged with `norm_num`,
  `ring`, or `field_simp` followed by `ring`.

Unsupported proof rules, propositions, objects, parameter types, composite
proofs, and inference origins stop compilation with an error. There is no
fallback to `axiom` or `sorry`.

The MVP also requires every cited global `FactId` to have been emitted earlier
in the same IR stream. Facts preloaded during ordinary execution still have
stable IDs, but compiling them through an external Lean library mapping is a
future backend feature; an unresolved preloaded ID is rejected instead of
becoming an undefined Lean name.

## Active tracer

[`examples/01_proof_patterns/to_lean_ir_mvp.lit`](../../examples/01_proof_patterns/to_lean_ir_mvp.lit)
covers the full first vertical slice: abstract proposition, concrete
proposition, trusted forall, known-forall instantiation, definition proof,
temporary-assumption reuse, forall introduction, and rational builtin proof.

Rust and Litex gates:

```text
cargo test --release to_lean:: -- --nocapture
target/release/litex -compact -isolated -runner -f examples/01_proof_patterns/to_lean_ir_mvp.lit
```

Actual Lean-kernel gate (requires an already-fetched Mathlib Lake project):

```text
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
  cargo test --release generated_to_lean_mvp_compiles_with_lean -- --ignored --nocapture
```

Implementation lives in `src/to_lean_ir`,
`src/runtime/runtime_to_lean_ir.rs`, and `src/to_lean`.
