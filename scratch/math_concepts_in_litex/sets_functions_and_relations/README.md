# Sets, Functions, and Relations

This independent first version checks three connected slices:

- set preimages, including positive and negative membership examples and the
  theorem that preimages preserve binary intersections;
- left, right, and two-sided inverse laws, a proof that a supplied two-sided
  inverse makes a function bijective, and the concrete `shift`/`unshift`
  bijection on `R`; and
- the integer `same_parity` relation, with checked reflexive, symmetric, and
  transitive laws plus a concrete witness.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r scratch/math_concepts_in_litex/sets_functions_and_relations
```

The module has no `trust` or local axiom. A general construction of an inverse
from an arbitrary bijection is still outside this first version; that direction
requires an explicit selection/choice interface rather than an invented
default-valued inverse.
