# Litex-to-Lean compiler

The compiler replays verifier-produced proof IR over one universal Lean object
type. It does not translate Litex set membership into Lean typing.

## Target ABI

Every Litex value, set, standard numeric set, function-space object, and
function value has target type `LitexObject`:

```lean
axiom LitexObject : Type
axiom Litex.In : LitexObject → LitexObject → Prop
axiom Litex.IsSet : LitexObject → Prop

def Litex.IsNonemptySet (s : LitexObject) : Prop :=
  Litex.IsSet s ∧ ∃ x : LitexObject, Litex.In x s

def Litex.IsFiniteSet (s : LitexObject) : Prop :=
  Litex.IsSet s ∧ Set.Finite {x : LitexObject | Litex.In x s}
```

For example, source `a C` contributes both an object binder and a membership
proof:

```lean
(a : LitexObject)
(haC : Litex.In a Litex.C)
```

If Litex later proves `a $in R`, the target retains a second proposition
`Litex.In a Litex.R`. The object is not converted from `ℂ` to `ℝ`; neither of
those native types is its Lean type.

`IsNonemptySet` and `IsFiniteSet` are not separate axioms. They classify an
object using primitive sethood and membership. The `Set.Finite` expression is
only a Mathlib view of the object's membership extension; source sets remain
`LitexObject` values.

The removed backend used native binders, `Set.univ : Set ℝ`, carrier joining,
widening, and downcast rejection. Those files and the carrier IR were deleted.
They are not a compatibility backend.

## Function objects

`fn(...) ...` is a `LitexObject` constructed from a restricted `Litex.FnSpec`.
The source application layers are preserved exactly:

```text
f(a, b) -> f [a, b] applicable_proof
f(a)(b) -> f [a] first_proof [b] second_proof
```

`Litex.Applicable f args` is constructed from the exact retained function-set
membership, argument memberships, and domain facts. Lean currying never makes
an invalid Litex application valid.

## Proof evidence

The parser and runtime assign stable `SourceObjectOccurrenceId`, `FactId`,
`WellDefinedFactId`, and `WellDefinedObjProofId` values while the successful
Litex scopes still exist. The backend consumes those IDs; it does not match
rendered propositions or rerun proof search.

- A known fact cites its exact `FactId`.
- A known forall cites its theorem `FactId`, explicit object arguments,
  parameter membership/set-property proofs, and domain proofs.
- A WD application argument cites a named helper derived from its exact
  `WellDefinedFactId`. If the proof occurs in a target theorem type, the helper
  is emitted first and generalized over the visible Litex environment.
- Equal source applications retain different occurrence IDs. If the second
  occurrence hits Litex's WD cache, both occurrence-use edges cite the same
  object proof and factual proof. The runtime labels preflight, proof, and
  store rechecks explicitly; the final target edge uses the proof scope when
  it exists and otherwise the preflight scope. The emitter never selects a
  candidate by whether Lean happens to prove it.
- A builtin certificate calls a real theorem under `Litex.BuiltinRules`.
  Concrete builtin rules are not axioms.
- Only explicit source `trust` may emit an axiom for the trusted proposition.

The small semantic core may declare the universal object universe,
membership, numeric embedding/coherence, restricted function application, and
primitive object constructors. This boundary interprets Litex. Ordinary
verifier rules are proved once from that core and Mathlib.

## Current strict slice

The replacement emitter currently covers the architecture tracer and its
supporting routes:

- abstract proposition declarations and explicit trusted facts;
- atomic equality, inequality, membership, and basic set predicates;
- standard sets and natural numerals;
- forall introduction and exact projected-forall `FactId`s;
- direct known facts and known-forall instantiation;
- equality transport and object reflexivity;
- closed numeral membership through proved builtin theorems;
- ordinary not-equality symmetry through a proved builtin theorem;
- named function spaces and exact one-layer or nested applications with named
  WD helpers and `Litex.fnSetResult` between layers;
- nested forall replay with retained temporary parameter `FactId`s;
- `Litex.add/sub/mul/div`, real arithmetic closure theorems, and rational
  normalization for the arithmetic tracer.

Unsupported statements or proof rules fail closed. They are not translated by
the deleted backend and do not become `sorry` or implicit axioms.

## Evidence

The primary acceptance source is
[`compile_to_lean_litex_object_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit).
The nested-forall/arithmetic/occurrence tracer is
[`compile_to_lean_arithmetic_forall_wd.lit`](../../examples/05_compiler_interop/compile_to_lean_arithmetic_forall_wd.lit).
The derived-set-predicate tracer is
[`compile_to_lean_set_predicate_definitions.lit`](../../examples/05_compiler_interop/compile_to_lean_set_predicate_definitions.lit).
The consolidated examples are in
[`compile_to_lean_examples.md`](../../examples/09_compile_to_lean/compile_to_lean_examples.md).

Focused Rust tests live beside `universal_pipeline.rs`. Ignored real-kernel
tests use `LITEX_LEAN_PROJECT` and optional `LITEX_LAKE` to compile the complete
generated source with Mathlib.
