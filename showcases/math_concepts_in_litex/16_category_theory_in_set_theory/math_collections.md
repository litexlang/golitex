# Mathematical design: small categories

## Chosen interface

Keep `Category<Obj, Mor>`, as selected on 2026-10-03. `Obj` is a set of
objects and `Mor` bounds arrow encodings. The fields are ordered:

```text
struct Category<Obj set, Mor set>:
    Hom fn(source, target Obj) power_set(Mor)
    identity fn(object Obj) Mor
    compose fn(source, middle, target Obj, f, g Mor: f $in Hom(source, middle), g $in Hom(middle, target)) Mor
    # <=>: exact Hom closure, identities, and associativity
```

A later field type may refer to earlier fields. A function's own parameter
names remain unavailable in its parameter carriers and return object; they
are available in its domain conditions and body. The `compose` field uses
one guarded call and a fixed `Mor` return carrier. Exact endpoint typing is
retained as category closure laws, not encoded as a dependent return type.

## Concepts and obligations

| Concept | Interface | Required mathematics |
| --- | --- | --- |
| Category | `Category<Obj, Mor>` | identity and composite Hom closure, both unit laws, associativity |
| Category data predicate | `is_category` | same laws on explicitly supplied Hom/identity/compose; used to check concrete data |
| Morphism, identity, selected composite | named propositions | precise Hom memberships and the corresponding equations |
| Functor | `is_functor` on source/target Category values and two maps | arrow Hom closure, identity preservation, composition preservation |
| Naturality square | `naturality_square_commutes` | input/image/component typing and one commuting square |
| Natural transformation | `is_natural_transformation` | two actual functors, component Hom closure, every naturality square |
| Constructions | existing named theorems | identity/composite functors, identity/vertical composite natural transformations |
| Concrete consumers | terminal and two-object chaotic categories | construct the data and prove the same laws; specialize identity functor |

Functor and natural-transformation assumptions must be present in their
composition theorems. Callable signatures alone do not imply preservation
or naturality. No trust or additional axioms are allowed for these proofs.
The natural-transformation definition also lists the two functors' arrow Hom
closures explicitly so composition goals can check their domains before the
proof body runs. These clauses follow from the existing functor assumptions;
`natural_transformation_from_naturality` verifies the same construction premise.

## Dependency order and verification boundary

`Hom and arrow relations -> Category -> category laws -> is_functor ->
identity/composite functors -> naturality -> identity/vertical composition ->
finite concrete consumers`.

Preserve the original named declarations and mathematical constructions.
Migration proceeds in this order in a persistent release session. On
2026-10-04 the complete Litex chapter
passed strict release (49/49 statements and the registered chapter gate).
Four derived closure lemmas expose exact Hom results before nested guarded
calls without changing the mathematical category, functor, or natural-transformation
requirements. The 2026-10-14 source repair repeats the functor arrow-closure
clauses inside the natural-transformation predicate so nested calls can check
their domains; the existing constructor proves these clauses from its original
functor premises. All 17 original named theorems and both finite constructions
remain present; no trust or axioms were added. The handwritten Lean analogy
was not revalidated in this proof-completion round.

Limits, colimits, adjunctions, Yoneda, universes, and a general functor category
remain outside this chapter's scope.
