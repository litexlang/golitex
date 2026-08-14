# Plan: Sets, Functions, and Relations

## Reader promise

This file teaches the common language used by later mathematics: a set is
something one can construct and test membership in; a function is something
one can apply and compose; a relation is something one can assert and prove
laws about. It should demonstrate Litex concept modeling without becoming a
foundations textbook.

## Mathematical boundary

Included:

- subset and extensional equality;
- union, intersection, and set difference through Builtin constructions;
- Cartesian products;
- function composition and restriction;
- image and preimage as set-valued constructions;
- injective, surjective, and bijective predicates;
- left inverse, right inverse, and two-sided inverse;
- binary relations, equivalence relations, and partial orders; and
- one small partition/equivalence-class example if the carrier remains
  explicit and usable.

Explicitly excluded:

- ZF/ZFC axiom development, ordinals, cardinals, transfinite recursion, and
  independence questions;
- category theory or a generic algebra-of-relations framework;
- quotient types before a real downstream consumer and stable representative
  interface exist;
- arbitrary choice as invisible infrastructure; and
- redeclaring native membership, subset, set builders, products, or function
  equality behind local aliases.

The stop rule is: this file supplies the smallest shared language needed by the
other four projects. A construction with no downstream theorem or example does
not enter merely because it appears in a set-theory syllabus.

## Internal architecture

1. **Native foundation**: Builtin sets, membership, subset, set builders,
   power sets, products, and functions.
2. **Set constructions**: union/intersection/difference laws and
   extensionality-driven proofs.
3. **Function constructions**: composition, restriction, image, and preimage.
4. **Function properties**: injective, surjective, bijective, and inverse
   laws.
5. **Relation properties**: reflexive, symmetric, transitive; equivalence and
   order interfaces.
6. **Flagship theorem**: a map has a two-sided inverse iff it is bijective,
   with the inverse exposed as an actual callable function when unique
   existence has been established.

## Main theorem chain

```text
membership and extensionality
  -> set operations
  -> composition/restriction
  -> image and preimage
  -> injective/surjective/bijective
  -> left and right inverses
  -> unique preimages under bijection
  -> selected inverse function
  -> two-sided inverse iff bijective
```

Relations form a parallel bounded branch:

```text
binary relation
  -> reflexive/symmetric/transitive
  -> equivalence relation
  -> equivalence classes and one partition example
```

Do not let the relation branch delay the function flagship. Quotient
construction is beyond the first boundary.

## Scratch example ladder

1. Preimage of the nonnegative reals under `x -> x + 1` -- current tracer;
   demonstrates why preimage must be a set-valued function.
2. Preimages preserve binary intersection -- first extensional proof.
3. Images preserve binary union -- first existential/preimage proof.
4. `x -> 2*x + 1` on `R` -- concrete inverse and two-sided checks.
5. General two-sided inverse implies bijective.
6. General bijective map has a uniquely selected inverse -- flagship, only
   after existence, uniqueness, and function well-definedness are explicit.

For relations, use congruence modulo a fixed positive natural as the one
concrete equivalence relation. Keep full modular arithmetic in number theory.

## Modeling decisions

- `set_preimage(B)` is `have fn ... power_set(S)`, because callers need to
  write membership and set equalities involving the result.
- `injective`, `surjective`, `is_left_inverse`, and `is_equivalence_relation`
  are `prop`, because they test supplied functions or relations.
- an inverse is not merely a relation. First model the candidate relation,
  prove unique existence on the intended domain, then expose the selected
  callable function.
- parameterized set-valued constructions use `template` only when their
  result carrier/declaration family genuinely depends on supplied carriers and
  functions.

## Lean comparison scene

Use preimage-intersection or inverse-of-bijection with identical mathematical
assumptions. Lean should be shown idiomatically with its native function and
set APIs; Litex should show the explicit construction and fact-oriented proof.
The comparison must disclose that Lean's type system and mathlib provide much
broader abstraction and reuse, while this Litex file intentionally favors a
small readable interface.

## Acceptance gates

- The file independently verifies with the release runner.
- No local wrapper duplicates a Builtin set concept.
- Every defined construction appears in a later theorem or flagship example.
- Image/preimage equality is proved extensionally, not postulated.
- Inverse selection exposes existence, uniqueness, domain, and codomain.
- No implicit choice or `trust` appears in the main spine.
- The project stops before quotient foundations and cardinal arithmetic.

## Expected downstream consumers

Number theory consumes relations and set-valued constructions; geometry
consumes loci and maps; linear algebra consumes subspaces, kernels, ranges,
images, preimages, and injectivity/surjectivity.
