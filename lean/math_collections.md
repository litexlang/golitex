# Mathematical Collections

## Scope

This document records the mathematical design of the v2 set system. The source
of truth is the single semantic bridge header `Litex/Core.lean`, the concrete
verifier-rule theorems in `Litex/Rules.lean`, and the same-name generated pairs
under `examples/`. Concept definitions and Lean/Mathlib representation bridges
must not be split into feature headers beside `Core.lean`.

The first unary function-set/application interface is included together with
the set system. The first ordered-numeric interface fixes how native Mathlib
order is reached without retyping Litex objects.

## Representation bridge

`Litex.BridgeRule α β` supplies a reviewed primitive representation relation,
and `Litex.Bridge x y` means that an installed rule relates `x` and `y`.
Numeric rules currently connect native naturals, integers, rationals, and
reals to their canonical complex embeddings. The subtype rule connects a
member of a predicate-defined carrier to its base value.

This primitive relation matters because reflexivity, symmetry, and
transitivity alone cannot create genuine cross-carrier equality.

Immediate use: `Litex.Same.complexReal r` relates `(r : ℂ)` to `r : ℝ`.

Nearest rejected form: silently treating all values of unrelated Lean types as
bridged. The executable boundary checks that the standard header installs no
primitive `Bool`-to-`Nat` bridge. A downstream Lean integration may explicitly
register another rule, but this is a trusted ABI extension rather than a
consequence of Litex source equality.

## Semantic equality

`Litex.Same x y` is the equivalence closure of `Litex.Bridge`. Native Lean
equality implies `Same` through `Litex.Same.ofEq`, while heterogeneous numeric
and subtype equality enters through `Same.base`.

Immediate use: a proof of `Same a b` transports `In a S` to `In b S` without
changing either Lean variable's carrier.

Open obligation: later extensional function and predicate interfaces must
state how they respect `Same`. The current unary wrapper is a proof-carrying
call interface; it does not claim function extensionality.

## Real representatives and order

`Litex.AsReal x r` is `Litex.Same x r` with `r : ℝ`. Consequently,
`Litex.In x Litex.R ↔ ∃ r, Litex.AsReal x r` holds definitionally. This keeps
real membership in the same object/set semantics instead of introducing a
second casting subsystem.

`Litex.Lt x y` and `Litex.Le x y` existentially select real representatives
and apply Mathlib's native `<` and `≤`. Both predicates transport across
`Same`. The rule `Lt x y → Le x y` needs no uniqueness assumption.

The registry remains extensible, so the core distinguishes choosing a
representative from identifying two representatives. `Litex.RealCoherence`
states the latter invariant. Irreflexivity, transitivity through independently
chosen middle representatives, and elimination to native Mathlib comparison
take this certificate explicitly. No inhabitant is postulated by the header.
An incoherent user bridge can only be combined with these elimination rules by
introducing a visibly trusted, false certificate.

## Exact-carrier sets

`Litex.Set` contains one field, `Carrier`. The carrier is the exact extension
of the represented set, not an ambient type paired with `Set.univ`.

For a new hidden mathematical carrier `__Marker`, the set is
`Litex.Set.ofType __Marker`. Every `marker : __Marker` belongs to it by
`Litex.In.own`.

For a predicate-defined subset, `Litex.setBuilder base predicate` uses the
subtype `{x : base.Carrier // predicate x}` as its exact carrier.

The construction remains universe-polymorphic. In particular,
`Litex.Set.{0} : Type 1`, so it may be the carrier of `Litex.Set.{1}`. A
generated example is deferred until compiler2 supports the corresponding
Litex statement form; the examples ledger contains no hand-written substitute.

Nearest rejected form: using the same carrier for a base set and a proper
subset. That would collapse their memberships.

## Heterogeneous membership

`Litex.In x S` means that some `y : S.Carrier` satisfies `Litex.Same x y`.
It is an ordinary proposition and never changes the Lean type of `x`.

The central use probe first defines the checked aliases `A = R` and `B = C`,
then starts with `a b : ℂ`, `a In A`, `b In B`, and `Same a b`, deriving
`b In A` and `a In B`. Its authoritative source is
`examples/1_SetSystem.lit`; the aliases become `Litex.Set` abbreviations and
verifier equality-rewrite evidence becomes `Litex.In.congr` in the paired
generated Lean file. A bare `have A set` is intentionally not synthesized by
the emitter: the verifier currently rejects that arbitrary choice because no
checked inhabited-type backend exists for the meta-level parameter type
`set`.

## Unary function sets and application

`Litex.Fn s S` contains one call field
`{α : Type u} → (x : α) → Litex.In x s → S.Carrier`. A value is
therefore not callable merely because of its Lean carrier: the call still
needs the Litex proof that its argument belongs to `s`.

`Litex.fnSet s S` packages `Fn s S` as an exact-carrier `Litex.Set`.
`Litex.fnApply f hf x hx` first selects the `Fn s S` representative supplied
by `hf : Litex.In f (Litex.fnSet s S)`, then calls it with
`hx : Litex.In x s`. Both proofs are explicit inputs. The result is directly
an `S.Carrier`; this wrapper layer has no inverse transport API.

The authoritative probe is `examples/4_FunctionSet.lit`. Its generated theorem
quantifies independent carriers for `x` and `f`, retains both membership
hypotheses, and emits both occurrences of `f(x)` with the exact
verifier-selected FactId/WD proofs. The nearest negative probe lives under
workspace-local `private/compiler2-function-set-test/`: changing `x s` to
`x S` is rejected by Litex before compiler2 emission.

The current boundary is intentionally narrow: one named unary layer, no extra
domain facts, no anonymous functions, no multiple arguments, and no curried
function return. Those forms remain unsupported rather than being flattened
to this ABI.

## Generated example contract

The `.lit` file is authoritative. Compiler2 first verifies it and captures the
exact `LitexToLeanStatementIr`; its native-carrier emitter validates and
consumes that IR. It does not reparse display text or search for a Lean proof.
A same-name `.lean` file is committed so reviewers can inspect the translation
without running the tool.

The drift gate recompiles each `.lit` in memory, compares the output byte for
byte, and invokes Lean on the checked-in result. Unsupported verified IR fails
closed. The initial reviewed routes are equality-based membership transport,
the fingerprinted `order.less_equal_of_less` registered rule, and top-level
closed numeric equality through verifier-selected reflexivity or rational
normalization. Numeric expression WD facts remain named local Lean facts.

Statement scope is also part of this contract. A Litex `sketch` becomes an
isolated `__SketchNN` Lean namespace with a cloned incoming compiler context;
its new symbol and FactId bindings are discarded when emission returns to the
file scope. A direct top-level fact is not placed in that namespace.

## Dependency order

```text
Mathlib native carriers
  -> Core.lean                  [single semantic bridge header]
  -> BridgeRule                 [controlled representation interface]
  -> Bridge                     [definition]
  -> Same                       [definition]
  -> Set                        [signature]
  -> In                         [definition: Same + Set.Carrier]
  -> Fn / fnSet                 [one unary proof-carrying function carrier]
  -> fnApply                    [consumes function + argument membership]
  -> numeric sets N/Z/Q/R/C     [definition]
  -> setBuilder                 [definition: subtype carrier]
  -> membership transport       [proof]
  -> AsReal                     [definition: Same + native real]
  -> RealCoherence              [certificate interface, no inhabitant assumed]
  -> Lt / Le                    [definition: native real order]
  -> order transport/bridges    [proof, still owned by Core.lean]
  -> Rules.lean                 [concrete verifier-certificate theorems]
  -> verifier-produced statement IR [checked compilation evidence]
  -> compiler2 strict emitter   [reviewed v2 adapters]
  -> same-name generated examples [real Lean proof]
```

There are currently no project-declared axiom or trust edges. A theorem may
take `RealCoherence` as an ordinary explicit typeclass parameter; that is not a
header axiom and remains visible in the generated theorem signature. The native
`ℝ`/`ℂ` examples retain Mathlib's foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound`). The next set-system decisions are
extensional set equality, union/intersection carriers, power-set universes,
and finiteness modulo `Same`.
