# Mathematical Collections

## Scope

This document records the mathematical design of the v2 set system. The source
of truth is the executable interface in `Litex/Core.lean`, the reusable facts
in `Litex/Rules.lean`, and the immediate use probes in
`examples/SetSystem.lean`.

Functions and compiler execution are intentionally outside this first slice.

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
respect `Same`. No such interface is claimed here.

## Exact-carrier sets

`Litex.Set` contains one field, `Carrier`. The carrier is the exact extension
of the represented set, not an ambient type paired with `Set.univ`.

For a new hidden mathematical carrier `__Marker`, the set is
`Litex.Set.ofType __Marker`. Every `marker : __Marker` belongs to it by
`Litex.In.own`.

For a predicate-defined subset, `Litex.setBuilder base predicate` uses the
subtype `{x : base.Carrier // predicate x}` as its exact carrier.

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
  -> executable examples        [proof]
```

There are currently no project-declared axiom or trust edges. The native
`ℝ`/`ℂ` examples retain Mathlib's foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound`). The next set-system decisions are
extensional set equality, union/intersection carriers, power-set universes,
and finiteness modulo `Same`.
