# Mathematical Design: Small Categories, Functors, and Natural Transformations

## Purpose and completion boundary

The target vertical slice is the standard first layer of category theory:

```text
CategorySetting
  -> FunctorSetting
  -> identity and composite functors
  -> NaturalTransformationSetting
  -> identity and vertically composed natural transformations
  -> terminal-category use
  -> STOP
```

This is complete enough to show why settings are useful when a mathematical
object carries a carrier, indexed hom-sets, operations, and laws. It is not a
general category-theory library. Limits, colimits, adjunctions, Yoneda, comma
categories, monads, functor categories as first-class categories, proper
classes, and universe hierarchies are explicit non-goals for this version.

## Core modeling decision

The data remain supplied explicitly and theorem contexts are bundled with
settings. A first-class `Category` struct is deliberately not introduced:
current consumers neither construct nor return a stored category value, and
dependent `Hom`, identity, and composition signatures are clearest at the
theorem boundary. The old flat category proposition and the setting must not
coexist as competing interfaces; `prop is_category([CategorySetting])` is the
single definition-facing projection of the same setting data and laws.

## Concept-to-interface map

| Concept | Ideal Litex form | Mathematical role |
| --- | --- | --- |
| small category | `setting CategorySetting(Obj, Mor, Hom, identity, compose)` | reusable ambient data and the unit/associativity laws |
| category predicate | `prop is_category([CategorySetting])` | tests the supplied category data without a second law list |
| morphism | `prop is_morphism(...)` | exposes hom-set membership for an ambient arrow candidate |
| selected composite | `prop is_composite(...)` | relates a candidate arrow to the supplied composition value |
| functor | `setting FunctorSetting([CategorySetting(C, ...)], [CategorySetting(D, ...)], object_map, arrow_map)` | two categories, two maps, identity preservation, and composition preservation |
| functor predicate | `prop is_functor([FunctorSetting])` | definition-facing projection of the functor setting |
| identity/composite functor | checked theorems with anonymous function values or local `let` aliases | genuine constructions; no one-use public adapter stack |
| natural transformation | `setting NaturalTransformationSetting([FunctorSetting(F)], [FunctorSetting(G)], component)` | parallel functors, typed components, and naturality |
| natural-transformation predicate | `prop is_natural_transformation([NaturalTransformationSetting])` | definition-facing projection of the transformation setting |
| identity/vertical composition | checked theorems | the first nontrivial algebra of natural transformations |

## Important interfaces

### `CategorySetting`

- **Ordinary meaning:** a set-sized collection of objects, set-bounded
  hom-sets, selected identities and composition, and the category laws.
- **Signature sketch:**

  ```litex
  setting CategorySetting(
      Obj, Mor set,
      Hom fn(source, target Obj) power_set(Mor),
      identity fn(object Obj) Hom(object, object),
      compose fn(source, middle, target Obj,
          f Hom(source, middle), g Hom(middle, target)) Hom(source, target)):
      # unit laws and associativity
  ```

- **Why `Mor` remains:** it is a set-theoretic bound for every hom-set. Hom
  indices already encode source and target, so separate `dom` and `cod`
  functions would add redundant coherence laws.
- **Dependency:** native sets, dependent function carriers, equality.
- **Downstream uses:** all functor and natural-transformation settings.
- **Allowable hole:** no first-class stored category value.

### `FunctorSetting`

- **Ordinary meaning:** `F : C -> D` maps objects and typed arrows and
  preserves identities and composition.
- **Signature sketch:** two renamed `CategorySetting` bundles, followed by
  `object_map : CObj -> DObj` and a dependent `arrow_map` from
  `CHom(X,Y)` to `DHom(FX,FY)`.
- **Nearest wrong alternative:** a flat predicate repeating two full category
  ABIs in every theorem. A struct is also premature because no current theorem
  stores a functor value or projects fields from one.
- **Downstream uses:** identity functor, functor composition, and both sides of
  a natural transformation.
- **Proof obligation:** identity and composition preservation are real laws;
  arrow typing is already enforced by the dependent return carrier.

### `NaturalTransformationSetting`

- **Ordinary meaning:** for parallel functors `F,G : C -> D`, every object
  `X` has a component `eta_X : F(X) -> G(X)`, and every arrow in `C` makes the
  naturality square commute.
- **Signature sketch:** two renamed `FunctorSetting` bundles sharing the same
  source and target category data, plus a dependent component function.
- **Nearest wrong alternative:** an untyped `component : CObj -> DMor` plus
  separate endpoint predicates. The dependent hom carrier is both shorter and
  stronger.
- **Downstream uses:** identity natural transformations and vertical
  composition.
- **Allowable hole:** horizontal composition and a general functor category
  are beyond the stop line.

## Typed dependency DAG

```text
Obj, Mor, Hom
  -> typed identity and composition
  -> CategorySetting
       -> is_category and existing finite category instances
       -> two renamed CategorySetting bundles
            -> typed object_map and arrow_map
            -> FunctorSetting
                 -> identity functor
                 -> composition of functors                 [primary tracer]
                 -> two parallel FunctorSetting bundles
                      -> typed component family
                      -> NaturalTransformationSetting
                           -> identity transformation
                           -> vertical composition
                           -> terminal-category end-to-end use
```

The graph is acyclic. Every reusable helper is either source-facing or has at
least two consumers. Repeated specializations may receive local role-based
`let` names, but public theorem statements stay in canonical spelling so
definition and theorem matching do not depend on reversing an alias.

## Source-aware implementation order

1. Preserve the existing morphism, identity, and composite relations.
2. Introduce `CategorySetting`; define `is_category` from it; migrate existing
   generic and finite-instance theorems to the same elaborated ABI.
3. Introduce `FunctorSetting` and `is_functor`; verify identity and composite
   functors.
4. Introduce `NaturalTransformationSetting` and its predicate; verify identity
   and vertical composition.
5. Reuse the checked terminal category as a concrete end-to-end consumer.
6. Stop at the explicit boundary above; do not add speculative wrappers for
   limits, adjunctions, or first-class category/functor records.

