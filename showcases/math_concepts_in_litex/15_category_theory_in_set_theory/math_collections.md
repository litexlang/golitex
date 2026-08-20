# Mathematical Design: Generic Small Categories in Set Theory

## Purpose and source of truth

This module models the standard data and laws of an arbitrary small category:
a set-sized object collection, a hom-set for each ordered pair of objects, an
identity arrow for each object, a typed composition operation, two unit laws,
and associativity. It then checks the terminal category and the two-object
chaotic category as concrete instances of that same interface.

The primary tracer is `category_composition_is_a_morphism`: for arbitrary
objects and arbitrary composable arrows, the dependent composition operation
returns an element of the expected endpoint hom-set. The other tracers expose
the selected identity and composite relations. The instance tracers are
`terminal_data_forms_a_category` and
`two_object_chaotic_data_forms_a_category`.

## Concept-to-interface map

| Category-theory concept | Litex form | Mathematical meaning |
| --- | --- | --- |
| objects | `Obj set` and `object Obj` | `Obj` is this category's object collection; `object` is an opaque member |
| ambient arrow bound | `Mor set` | one set containing the encodings used by all hom-sets |
| hom-set | `Hom fn(source, target Obj) power_set(Mor)` | `Hom(A, B)` is the set of arrows from `A` to `B` |
| morphism relation | `is_morphism(..., A, B, f)` | an ambient candidate `f` belongs to `Hom(A, B)` |
| identity data | `identity fn(object Obj) Hom(object, object)` | chooses an actual endomorphism for every object |
| identity property | `is_identity_morphism` | the candidate is neutral for composition on both sides |
| composition data | dependent `compose` function | sends `f : A -> B` and `g : B -> D` to `g after f : A -> D` |
| composite relation | `is_composite(..., f, g, h)` | candidate `h` equals the selected composition value |
| category laws | `is_category(...)` | selected identities obey both unit laws and composition is associative |
| terminal category | `terminal_*` data | one object and one arrow; every hom-set is `{0}` |
| two-object chaotic category | `two_object_*` data | `Hom(A,B) = {(A,B)}` gives exactly one arrow for every ordered pair |

## Modeling decisions

### Objects are opaque members of `Obj`

- **Ordinary meaning:** Category objects are characterized by their role in a
  category, not by a requirement that they all have one internal shape.
- **Litex form:** `Obj set`, followed by binders such as `source Obj`.
- **Important distinction:** `source Obj` means `source $in Obj`; it does not
  imply `$is_set(source)` and does not need to.
- **Why this form:** `Hom` uses objects only as indices. A later concrete
  instance may use encodings of sets, groups, spaces, or other structures.
- **Rejected alternative:** `Obj = power_set(U)` would select a particular
  category whose objects are subsets and would no longer be the generic
  category structure requested here.

### Hom-family with an ambient morphism set

- **Ordinary meaning:** Every ordered pair `(A, B)` has a set of arrows
  `Hom(A, B)`.
- **Litex form:** `Mor set` and
  `Hom fn(hom_source, hom_target Obj) power_set(Mor)`.
- **Why `Mor` is present:** Litex does not treat the unrestricted collection
  of all sets as a set-valued function codomain. `power_set(Mor)` gives each
  hom-set an explicit set-theoretic bound.
- **Why no `dom` and `cod`:** Hom indices already carry endpoint information.
  Adding independent endpoint functions would require extra coherence laws.
- **Boundary:** `Mor` may contain unused encodings; the mathematical arrows
  are the elements of the individual hom-sets.

### Dependent identity and composition carriers

- **Identity signature:**
  `identity fn(identity_object Obj) Hom(identity_object, identity_object)`.
- **Composition signature:** Inputs include three objects and two precisely
  typed arrows; the result carrier is `Hom(comp_source, comp_target)`.
- **Consequence:** Identity typing and composition closure are enforced by the
  signatures. `is_category` need not repeat them as propositions.
- **Composition convention:**
  `compose(source, middle, target, f, g)` denotes `g` after `f`.

### Flat propositions instead of a category struct

- **Ordinary meaning:** A tuple of supplied data satisfies the category laws.
- **Litex form:** `is_category(Obj, Mor, Hom, identity, compose)` with nested
  `forall` clauses.
- **Why this form:** The Hom, identity, and composition carriers depend on
  earlier parameters. A flat proposition represents that dependency directly
  and follows the requested `prop`/`forall` style.
- **Non-goal:** This module does not make category values constructible,
  storable, or returnable as one first-class Litex object.

### Explicit auxiliary predicates

- `is_morphism` is useful for a candidate known only as `f Mor`; a binder
  `f Hom(A, B)` already carries the same fact.
- `is_identity_morphism` defines identity behavior independently of the
  selected `identity` function.
- `is_composite` relates an arbitrary correctly typed candidate to the actual
  result selected by `compose`.

## Dependency map

```text
Obj set, Mor set
  -> Hom : Obj x Obj -> power_set(Mor)                   [signature]
       -> is_morphism                                   [definition]
       -> identity(A) : Hom(A, A)                       [signature]
       -> compose(A, B, D, f, g) : Hom(A, D)            [signature]
            -> is_identity_morphism                     [definition]
            -> is_composite                             [definition]
            -> is_category                              [unit + associativity]
                 -> selected identity tracer            [proof]
       -> composition-is-a-morphism tracer              [proof]
       -> selected-composite tracer                     [proof]
  -> terminal_*                                         [finite instance]
       -> terminal_data_forms_a_category                [proof]
  -> two_object_*                                       [finite instance]
       -> two_object_chaotic_data_forms_a_category      [proof]
```

There is no dependency cycle and no new parser, verifier, or kernel capability
is required.

## Public boundary and future work

The module deliberately stops after two illustrative finite instances. It does
not develop functors, natural transformations, universal constructions, large
categories, proper classes, or universe hierarchies. A future library can
place a reusable setting or first-class representation above this verified
flat interface once real consumers determine the required ABI.

The public artifacts contain no direct `trust`, global axiom,
`abstract_prop`, Lean `axiom`, `sorry`, or `admit`.
