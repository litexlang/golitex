# Mathematical Collections

## Scope

This document records the mathematical design of the v2 set system. The source
of truth is the executable interface in `Litex/Core.lean`, the reusable facts
in `Litex/Rules.lean`, and the immediate use probes in
`examples/SetSystem.lean`.

Functions and compiler execution are intentionally outside this first slice.
The first ordered-numeric interface is included because it fixes how native
Mathlib order is reached without retyping Litex objects.

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

Open obligation: later function and predicate interfaces must explicitly
respect `Same`. The ordered-numeric predicates below are the first executable
instance of that rule.

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
`Litex.Set.{0} : Type 1`, and `SetSystem.lean` defines a `Litex.Set.{1}` whose
carrier is `Litex.Set.{0}` and proves that `R` belongs to it.

Nearest rejected form: using the same carrier for a base set and a proper
subset. That would collapse their memberships.

## Heterogeneous membership

`Litex.In x S` means that some `y : S.Carrier` satisfies `Litex.Same x y`.
It is an ordinary proposition and never changes the Lean type of `x`.

The central use probe starts with `a b : ℂ`, `a In R`, `b In C`, and
`Same a b`, then derives `b In R` and `a In C`. Its generated names follow the
existing compiler ledger convention: `__SetSystem01.__fact0` and `__h0_*`.

## Dependency order

```text
Mathlib native carriers
  -> BridgeRule                 [controlled representation interface]
  -> Bridge                     [definition]
  -> Same                       [definition]
  -> Set                        [signature]
  -> In                         [definition: Same + Set.Carrier]
  -> numeric sets N/Z/Q/R/C     [definition]
  -> setBuilder                 [definition: subtype carrier]
  -> membership transport       [proof]
  -> AsReal                     [definition: Same + native real]
  -> RealCoherence              [certificate interface, no inhabitant assumed]
  -> Lt / Le                    [definition: native real order]
  -> order transport/bridges    [proof]
  -> executable examples        [proof]
```

There are currently no project-declared axiom or trust edges. A theorem may
take `RealCoherence` as an ordinary explicit typeclass parameter; that is not a
header axiom and remains visible in the generated theorem signature. The native
`ℝ`/`ℂ` examples retain Mathlib's foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound`). The next set-system decisions are
extensional set equality, union/intersection carriers, power-set universes,
and finiteness modulo `Same`.
