# Small Categories in Set Theory: Generic Data and Examples

This showcase develops small categories, functors, natural transformations,
and two finite examples. The complete Litex chapter passes strict release
verification: **49/49 top-level statements**, including all 17 original
named theorems and four derived Hom-closure lemmas. The selected interface
is `Category<Obj, Mor>` with ordered dependent fields, fixed function return
carriers, and guarded composition. All original named declarations remain
active, with no trust or extra axioms. The proof-completion round changed
Litex source and records only; see the [acceptance record](../../../scripts/math_concepts_in_litex_upstream/experience/problem_notes/category_proof_completion_acceptance.md).

The standalone [Category regression](../../../examples/wd/category_dependent_fields.lit)
checks the two-parameter struct, unit/associativity laws, and an actual guarded
identity-composition call. The intended chapter sequence is:

```text
Obj set
  -> Mor set
  -> Hom(A, B) subset Mor for every A, B in Obj
  -> identity(A) in Hom(A, A)
  -> compose(A, B, D, f, g) in Hom(A, D)
  -> two unit laws and associativity
  -> typed object and arrow maps
  -> identity and composite functors
  -> typed components and naturality squares
  -> identity and vertical composition of natural transformations
```

Run the chapter from the repository root:

```bash
target/release/litex -strict -f showcases/math_concepts_in_litex/16_category_theory_in_set_theory/main.lit
target/release/litex -strict -r showcases/math_concepts_in_litex/16_category_theory_in_set_theory
```

Run the handwritten Lean analogy with the repository's Lean toolchain:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/16_category_theory_in_set_theory/same_math_in_lean.lean
```

## What `Obj` means

Category theory normally speaks at a higher level of abstraction than the
internal definitions of its objects. An object may play the role of a set, a
group, a topological space, a type, or another category. The same categorical
language then studies arrows, identities, and composition without repeatedly
opening those internal structures.

That is an abstraction claim, not a claim that category theory is logically
outside set theory. Standard set-theoretic foundations can encode every small
category. This showcase does so with `Obj set`: `Obj` is the set-sized
collection of objects in one category, and `A Obj` means that `A` is one of
those objects. It deliberately does **not** assert `$is_set(A)`. An object is
an opaque index here, not necessarily a function carrier and not necessarily
an object of the category of sets.

Concrete mathematics enters by choosing data satisfying this generic
interface. For example, a category of groups would choose group values as the
members of `Obj` and group homomorphisms as the corresponding hom-sets. The
generic definitions do not assume that choice; the final part of this file
contains two deliberately tiny finite category constructions with checked
unit and associativity laws.

## Why both `Mor` and `Hom` appear

The ideal mathematical notation says that `Hom(A, B)` is a set for every pair
of objects. Litex does not use an unrestricted "set of all sets" as a function
codomain, so the interface supplies one ambient set `Mor` of arrow encodings:

```text
Hom fn(hom_source, hom_target Obj) power_set(Mor)
```

Thus every `Hom(A, B)` is a subset of `Mor`. The ambient carrier is a
set-theoretic bound; `Hom(A, B)` is still the precise type of arrows from `A`
to `B`. Elements of `Mor` not used by any hom-set are harmless representation
redundancy. This design does not also introduce `dom` and `cod`, because the
two Hom indices already record the endpoints.

## The generic category data

- `Obj set` is the collection of objects.
- `Mor set` is the ambient collection of arrow encodings.
- `Hom(A, B)` is the set of morphisms from `A` to `B`.
- `identity(A)` is an actual value in `Hom(A, A)`.
- `compose(A, B, D, f, g)` is the actual value `g` after `f` in
  `Hom(A, D)`.
- `is_category(...)` requires the two unit laws and associativity.

Function return carriers are fixed. `identity` and `compose` return `Mor`;
the exact Hom output memberships are explicit category laws. `compose` retains
one call with domain conditions on its two input arrows.

`Category<Obj, Mor>` stores `Hom`, `identity`, and `compose` in that order.
The `compose` field type may refer to the earlier `Hom` field. This does not
allow a function's own parameters in its parameter carriers or return object.
The category theorem contexts bind an actual Category value, which supplies
closure, both unit laws, and associativity. `is_functor` and
`is_natural_transformation` retain precise arrow/component typing as explicit
laws. Composition theorems also require the actual functor or naturality
premises; function signatures alone never establish them.

The identity and composite functor theorems and the identity and vertical
natural-transformation theorems are genuine constructions. Their callable
maps and component families use local `let` names so diagram proofs remain
readable without adding public one-use adapters.

## Explicit relation names

The auxiliary propositions make the usual words visible:

- `is_morphism(..., A, B, f)` tests whether an ambient candidate `f Mor`
  belongs to `Hom(A, B)`;
- `is_identity_morphism(..., A, identity_arrow)` states both unit properties
  for a candidate endomorphism; and
- `is_composite(..., f, g, h)` states that `h` equals the selected composite
  of `f` and `g`.

If a binder already says `f Hom(A, B)`, then `f` is already known to be a
morphism and `is_morphism` is logically redundant. It remains useful when the
candidate starts only as an element of the ambient `Mor` set, and it makes the
concept mapping explicit for readers.

The three tracer theorems verify that the selected identity has the identity
property, composition produces a morphism with the expected
endpoints, and the selected composition value satisfies `is_composite`.
Derived Hom-closure lemmas establish the exact carriers of mapped identities,
mapped compositions, composite arrows, and vertical components before guarded
nested calls. Named `composition_is_associative_at` and `naturality_square_commutes`
properties let larger diagram proofs select an exact instance before
unfolding it to an equality.

## Two concrete categories

The terminal example chooses

```text
Obj = {0}
Mor = {0}
Hom(A, B) = {0}
identity(A) = 0
compose(A, B, C, f, g) = 0
```

There is one object and one arrow, so both unit laws and associativity reduce
to uniqueness of the member of `{0}`. The theorem
`terminal_data_forms_a_category` checks these data against the generic
`is_category` predicate. `terminal_identity_functor_exists` then reuses the
generic identity-functor construction as an end-to-end concrete consumer.

The two-object chaotic example chooses

```text
Obj = {0, 1}
Mor = Obj x Obj
Hom(A, B) = {(A, B)}
identity(A) = (A, A)
compose(A, B, C, (A, B), (B, C)) = (A, C)
```

Thus every ordered pair of objects has exactly one arrow. This is the chaotic
(also called indiscrete) category, not the discrete category: in particular,
there is an arrow from `0` to `1` and an arrow from `1` to `0`. The theorem
`two_object_chaotic_data_forms_a_category` states its unit and associativity
laws through the same generic interface.

## Exact scope boundary

The intended scope boundary is: small categories, functors,
identity/composite functors, natural transformations, identity/vertical
composition, and a concrete terminal-category consumer. It does not define:

- the large category of all sets, groups, or categories;
- proper classes or universe-level stratification;
- limits, colimits, adjunctions, Yoneda, comma categories, monads, or a
  general functor category;
- automatic category instances for existing Litex structures.

The public Litex file contains no direct `trust`, global `axiom`, or
`abstract_prop`. The Lean file is handwritten comparison material; it was not revalidated
in this migration.

## Current callable interfaces

The identity-component lemma accepts a named function with its exact pointwise identity specification. The identity natural transformation theorem constructs that function and proves the specification before using the lemma.
