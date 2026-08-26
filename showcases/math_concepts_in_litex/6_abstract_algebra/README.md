# Abstract Algebra

This settings-first showcase now has two checked vertical slices.

The group slice defines groups, homomorphisms, subgroups, and normal
subgroups; proves cancellation and uniqueness laws; proves that
homomorphisms preserve identity and inverse; and proves that a group
homomorphism's native set-builder kernel is normal.

The commutative-ring slice defines ring homomorphisms, ideals, prime ideals,
integral domains, and fields. It proves that a ring-homomorphism kernel is an
ideal and models a quotient by the data actually consumed by quotient
theorems: a surjective ring homomorphism with exact kernel. The two flagship
theorems prove both directions of

```text
I is prime  <=>  the supplied quotient presentation is an integral domain.
```

The ordinary integer operations provide a checked concrete ring instance.

This is the stopping boundary for the first version. It does not construct
quotient equivalence classes, prove the maximal-ideal/quotient-field theorem,
or develop finite fields, polynomial rings, PID/UFD theory, modules, field
extensions, or Galois theory. Algebraic geometry, homological algebra,
representation theory, model theory, and universal algebra are collection
non-goals, not missing chapters.

`main.lit` contains no `trust`. The independent release file and module
runners must both return top-level `ok: true`. See `math_collections.md` for
the exact interface and boundary decisions.

`same_math_in_lean.lean` expresses the same progression using
only Lean's automatically loaded Prelude: it has no imports and does not depend
on Mathlib. It is a handwritten formulation of the same semantics, not generated output and not
a claim about the Litex-to-Lean compiler's current function or group support.
Run it independently with:

```sh
lean showcases/math_concepts_in_litex/6_abstract_algebra/same_math_in_lean.lean
```
