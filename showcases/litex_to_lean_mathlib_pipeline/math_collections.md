# Mathematical Design: Litex to Mathlib Pipeline

## Purpose and scope

This module owns one dependency-closed theorem and one real downstream use. It
is intentionally thinner than a textbook chapter: completion is measured by
whether the verified fact enters Lean/Mathlib and creates reusable value, not
by the amount of Litex source written.

## Interface cards

### Strict order implies non-strict order

- **Natural meaning:** if real `a` is strictly smaller than real `b`, then it
  is also no greater than `b`.
- **Litex form:** a named `thm` over two `R` binders with one domain premise
  and one conclusion.
- **Verification evidence:** the conclusion retains the allowlisted typed
  strict-to-weak order rule and the checked strict-order premise.
- **Canonical Lean view:** exact Litex carriers, membership representatives,
  and the proof constructor selected by the verifier remain visible.
- **Native Lean view:** `(a b : ℝ) → a < b → a ≤ b`, emitted only after the
  source shape and proof evidence pass the closed allowlist.
- **Downstream consumer:** nonemptiness of Mathlib's `Set.Icc a b`, proved in
  a different Lean module that imports the generated theorem.
- **Rejected shortcut:** a general `Litex.Same → Eq` bridge or an assumption
  that `Classical.choose` returns a particular membership witness would widen
  the trust boundary and is not needed for this theorem.

## Dependency spine

```text
natural order statement
  -> Litex theorem
  -> typed strict-to-weak proof evidence
  -> canonical Lean theorem                         [audit view]
  -> native real-order replay through OrderBridge   [reuse view]
  -> Lean kernel acceptance
  -> Set.Icc nonempty                               [downstream value]
```

## Current export boundary

The native emitter requires exactly two direct real parameters, matching left
and right operands in `a < b` and `a <= b`, and the typed arithmetic evidence
for strict-to-weak order. Any mismatch leaves the native declaration absent;
the canonical theorem remains available. This boundary is tested by a nearby
real-equality theorem that must not acquire a native declaration.
