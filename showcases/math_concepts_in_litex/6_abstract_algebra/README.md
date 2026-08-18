# Abstract Algebra

This settings-first group-theory showcase has a checked first checkpoint. It
defines first-class group and group-homomorphism predicates, uses named settings
for ambient theorem contexts, composes the homomorphism setting from two group
bundles, states the standard two-sided group laws, proves cancellation and
uniqueness of identity and inverse, and proves that a homomorphism preserves
identity and inverse. Its flagship theorem then uses the native kernel set
builder to prove that the kernel of a group homomorphism is a normal subgroup.
Its proofs use `by thm ... => fact` to name the exact atomic consequence that
each theorem application contributes to the next mathematical step.

`main.lit` contains no `trust`. Both the independent release file runner and
module runner return top-level `ok: true`. See `math_collections.md` for the
fixed scope and interface decisions.

`same_math_in_lean.lean` expresses the same progression using
only Lean's automatically loaded Prelude: it has no imports and does not depend
on Mathlib. It is a handwritten formulation of the same semantics, not generated output and not
a claim about the Litex-to-Lean compiler's current function or group support.
Run it independently with:

```sh
lean showcases/math_concepts_in_litex/6_abstract_algebra/same_math_in_lean.lean
```
