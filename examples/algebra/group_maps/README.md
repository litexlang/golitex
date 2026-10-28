# Group maps and subgroup transport

Homomorphisms carry group multiplication through ordinary functions. This
example follows integer doubling and tripling through native composition,
then uses actual function ranges and inverse images as subgroup constructions.
The same source laws permit trivial and noncommutative groups.

The following complete generic caller shows the order of composition. The
map f goes from the first group to the second; g goes from the second to
the third. Their composite is the existing native object compose(g,f).

```litex
thm composed_group_map:
    ? forall A nonempty_set,G &Algebra::group::Group<A>,B nonempty_set,H &Algebra::group::Group<B>,D nonempty_set,K &Algebra::group::Group<D>,f fn(x A) B,g fn(y B) D:
        $Algebra::group::is_homomorphism(A,G,B,H,f)
        $Algebra::group::is_homomorphism(B,H,D,K,g)
        =>:
            $Algebra::group::is_homomorphism(A,G,D,K,compose(g,f))
    release thm Algebra::group::homomorphism_composition(A,G,B,H,D,K,f,g)
```

In [main.lit](main.lit), double(x)=2*x and triple(x)=3*x are homomorphisms
of integer addition. Their composite sends5 to30. The image of double is
a subgroup containing6. The inverse image of {0} under double is {0}; for
the zero map it is all of Z. These sets retain the ambient group's operations.
The one-element group also satisfies the same laws.

The [noncommutative consumer](noncommutative/main.lit) reuses the checked
Heisenberg group and its zero projection from the existing model. Named model
facts supply the group laws, identity, noncommutativity and projection formula.
The projection image is the singleton identity, and the same source interfaces
prove subgroup/normal inverse images and a composite homomorphism. No second
group or map definition is introduced.

Whole-carrier and singleton-identity subgroup laws supply elementary targets.
Intersection preserves normality when both inputs are normal. A homomorphism
range is always a subgroup of its target; no target-normality claim follows.
A normal inverse-image theorem keeps its target normality premise, without
requiring the source or target group to be commutative.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Integer/trivial groups, composition, images and normal inverse images |
| [noncommutative/main.lit](noncommutative/main.lit) | Reused Heisenberg group, zero projection, image, composition and normal inverse images |
| [contracts/main.lit](contracts/main.lit) | All eight source signatures with their original domains and premises |
| [readme/main.lit](readme/main.lit) | The isolated generic composite-map caller above |
| [negative/expected.json](negative/expected.json) | Required premises, map carriers/arity and false values/conclusions |

The group export uses existing native maps/sets and checked source theorems.
It adds no new group operation, trust, search rule or compiler implementation.
Quotient groups, Lagrange and isomorphism theorems remain separate work.
