# Mathematical Collections

This module is an executable map of the current Litex-to-Lean interface rather
than a new mathematical theory. Its central collection is the set of source
judgments whose verifier evidence has a checked native Mathlib interpretation.

## Native numeric carriers

Litex standard-set objects `N`, `Z`, `Q`, `R`, and `C` denote universal sets
over Mathlib's `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ`. A numeral has no intrinsic source
carrier. Membership, a bounded parameter, or another checked judgment supplies
the target expectation only where needed.

The representative interface is:

```litex
2 $in R

forall z Z:
    z / 2 $in Q
```

The intended Lean shapes are `2 ∈ (Set.univ : Set ℝ)` and
`(z / 2 : ℚ) ∈ (Set.univ : Set ℚ)`. The nearest rejected shape is a
closed ambiguous division admitted only by `trust`; proof provenance must not
select its carrier.

## Facts and proof evidence

Facts remain propositions rather than objects. Bounded universal facts retain
both the native binder carrier and their membership premises. Native equality,
arithmetic, order, and supported set operations are emitted directly. An
explicit Litex `trust` is the only source construct in this repository that may
become a Lean axiom.

The examples cover direct facts, definition reduction, known-forall
instantiation, equality transport, rational normalization, typed builtin
rules, recursive additive evidence, checked choice, existential introduction
and elimination, case splitting, and contradiction scopes.

`carrier_boundaries.lit` keeps source facts that Litex verifies but whose
current proof route is not fully represented by the strict backend. This
includes several numeric membership-closure facts and `have` value checks over
`N`, `Z`, `Q`, and `C`. Their native target carriers are settled; their missing
proof backends are reported rather than replaced.

The strict object-definition example uses a real numeral. A real division
definition is left as a commented boundary because Mathlib requires that
generated declaration to be `noncomputable`; accepting the Litex source alone
is not counted as successful backend coverage.

## Native sets

A general Litex set parameter becomes `Set α` for one implicit element
carrier. `union`, `intersect`, and `set_minus` map to native Mathlib set
operations. This avoids a monomorphic `LitexSet` universe while preserving the
source claim that all Litex objects satisfy `$is_set` through a polymorphic
object marker.

Binder-owning set builders and several richer object families remain outside
this executable collection. They are not approximated by axioms or custom
equality.

## Honest incomplete output

The two boundary files record the distinction between source verification and
backend coverage. In particular, report-mode To-Lean omits the currently
unsupported `sin(0) = 0`, emits both surrounding rational facts, and reports
`Incomplete`. These boundaries are intentional and have no proof, existence,
uniqueness, or hidden-trust workaround.
