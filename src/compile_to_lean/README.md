# Litex-to-Lean compiler

The compiler replays verifier-produced proof IR over one universal Lean object
type. It does not translate Litex set membership into Lean typing.

The consolidated target design and its ten representative examples are in
[`litex_object_design.md`](litex_object_design.md). The shared ABI is owned by
[`Litex.Core`](../../lean/Litex/Core.lean), concrete builtin theorems by
[`Litex.BuiltinRules`](../../lean/Litex/BuiltinRules.lean), and the exact import
plus ABI check emitted today is checked in as
[`current_generated_file_header.lean`](current_generated_file_header.lean).
The design ledger explicitly marks decisions that the current emitter has not
implemented yet.

## Target ABI

Every Litex value, set, standard numeric set, function-space object, and
function value has target type `Litex.Object`:

```lean
namespace Litex

axiom Object : Type
axiom In : Object → Object → Prop
def IsSet (_ : Object) : Prop := True

def IsNonemptySet (s : Object) : Prop :=
  ∃ x : Object, In x s

def IsFiniteSet (s : Object) : Prop :=
  Set.Finite {x : Object | In x s}

end Litex
```

For example, source `a C` contributes both an object binder and a membership
proof:

```lean
(a : Litex.Object)
(haC : Litex.In a Litex.C)
```

If Litex later proves `a $in R`, the target retains a second proposition
`Litex.In a Litex.R`. The object is not converted from `ℂ` to `ℝ`; neither of
those native types is its Lean type.

Every `Litex.Object` is a set in the decided target model. `IsNonemptySet` and
`IsFiniteSet` are not separate axioms; they classify the object's membership
extension. The `Set.Finite` expression is only a Mathlib view of that
extension; source sets remain `Litex.Object` values. The shared `Litex.Core`
implementation still defines opaque `IsSet` plus redundant conjuncts; see
[`Litex.Core`](../../lean/Litex/Core.lean) for that explicit migration debt.

The builtin `$is_choice_function_for(I,S,g,f)` is likewise emitted as the
defined proposition `Litex.IsChoiceFunctionFor I S g f`, quantified over
members of `I` and the exact applicability proofs for `f` and `g`. It is not an
uninterpreted target axiom. The `S` argument remains in the public arity while
its carrier obligations are supplied by Litex well-definedness.

The removed backend used native binders, `Set.univ : Set ℝ`, carrier joining,
widening, and downcast rejection. Those files and the carrier IR were deleted.
They are not a compatibility backend.

## Function objects

`fn(...) ...` is a `Litex.Object` constructed from a restricted `Litex.FnSpec`.
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
- A known equality-class proof freezes an ordered path of direct equality
  `FactId`s. The emitter validates every edge and replays only `Eq.symm` and
  `Eq.trans`; it never searches the equivalence class again.
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
- A builtin certificate calls a real theorem imported from the shared
  `Litex.BuiltinRules` module. Concrete builtin rules are not axioms.
- Only explicit source `trust` may emit an axiom for the trusted proposition.

The shared `Litex.Core` module declares the universal object universe,
membership, numeric embedding/coherence, restricted function application, and
primitive object constructors. This boundary interprets Litex. Ordinary
verifier rules are proved once in `Litex.BuiltinRules` from that core and
Mathlib; generated files import the module and never repeat those proof bodies.

## Current strict slice

The replacement emitter currently covers the architecture tracer and its
supporting routes:

- abstract proposition declarations and explicit trusted facts;
- atomic equality, inequality, membership, and basic set predicates;
- standard sets and natural numerals;
- forall introduction and exact projected-forall `FactId`s;
- direct known facts and known-forall instantiation;
- equality transport and object reflexivity;
- direct known-equality symmetry and transitivity through exact `FactId`
  paths;
- closed numeral membership through proved builtin theorems;
- ordinary not-equality symmetry through a proved builtin theorem;
- named function spaces and exact one-layer or nested applications with named
  WD helpers and `Litex.fnSetResult` between layers;
- nested forall replay with retained temporary parameter `FactId`s;
- `Litex.add/sub/mul/div`, real arithmetic closure theorems, and rational
  normalization for the arithmetic tracer.

Unsupported statements or proof rules fail closed. They are not translated by
the deleted backend and do not become `sorry` or implicit axioms.
In particular, the current strict slice does not yet replay the
`by axiom_of_choice` or `by zorn_lemma` statement certificates, nor does it yet
lower every `general_cart`/`big_union` object. The named choice predicate has a
target meaning now; those larger constructors still require their own checked
IR and theorem routes before complete choice examples can compile.

## Evidence

The primary acceptance source is
[`compile_to_lean_litex_object_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit).
The shared-builtin-library tracer is
[`compile_to_lean_shared_builtin_rules.lit`](../../examples/05_compiler_interop/compile_to_lean_shared_builtin_rules.lit).
The nested-forall/arithmetic/occurrence tracer is
[`compile_to_lean_arithmetic_forall_wd.lit`](../../examples/05_compiler_interop/compile_to_lean_arithmetic_forall_wd.lit).
The derived-set-predicate tracer is
[`compile_to_lean_set_predicate_definitions.lit`](../../examples/05_compiler_interop/compile_to_lean_set_predicate_definitions.lit).
The known-equality path tracer is
[`compile_to_lean_known_equality_path.lit`](../../examples/05_compiler_interop/compile_to_lean_known_equality_path.lit).
The consolidated examples are in
[`compile_to_lean_examples.md`](../../examples/09_compile_to_lean/compile_to_lean_examples.md).

Focused Rust tests live beside `universal_pipeline.rs`. Ignored real-kernel
tests use `LITEX_LEAN_PROJECT` and optional `LITEX_LAKE` to compile
`Litex.Core`, `Litex.BuiltinRules`, and the complete generated source with
Mathlib.
