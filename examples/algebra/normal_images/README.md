# Normal subgroup images and composition kernels

A subgroup image uses its actual carrier and the ambient group operations.
A surjective homomorphism sends a normal subgroup to a normal subgroup of the
whole target. This example develops those laws alongside a kernel identity
that only needs ordinary complete maps.

The composition kernel is the inverse image of the second kernel. The following
complete generic caller needs only the target group K; neither a source/middle
group nor a homomorphism premise is required for this set equality.

```litex
thm composite_kernel:
    ? forall A nonempty_set,B nonempty_set,D nonempty_set,K &Algebra::group::Group<D>,f fn(x A) B,g fn(y B) D:
        \Algebra::group::kernel<A,D,K,compose(g,f)> = preimage_set(f,\Algebra::group::kernel<B,D,K,g>)
    release thm Algebra::group::kernel_of_composition(A,B,D,K,f,g)
```

In [main.lit](main.lit), shift(x)=x+1 is explicitly proved not to be a
homomorphism of integer addition, while double(x)=2*x is one. The composite
sends5 to12 and its kernel is {-1}. The same set is the inverse image under
shift of double's kernel. This kernel is not asserted to be a subgroup.

Doubling sends the identity subgroup to {0}. Negation is a surjective
homomorphism; the normal-image law applies both to {0} and to all Z. The image
is fn_range(fn(t S) B {f(t)}), so no unrelated operations or new image selector
are placed on S. Surjectivity is onto the whole target B, not just fn_range(f).

The [one-point model](trivial/main.lit) checks the allowed trivial group. Its
nonempty carrier, identity membership and operation signatures are explicitly
checked before constructing the group. The [noncommutative caller](noncommutative/main.lit)
reuses the existing Heisenberg group and projection. It checks normal identity/
whole subgroups, subgroup images, normal images under the surjective identity
and projection/composite kernels equal to the whole carrier.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Integer normal images and a non-homomorphism composition kernel |
| [trivial/main.lit](trivial/main.lit) | All five interfaces on a one-point group |
| [noncommutative/main.lit](noncommutative/main.lit) | Existing Heisenberg model with no commutativity premise |
| [contracts/main.lit](contracts/main.lit) | Exact five source signatures and guards |
| [readme/main.lit](readme/main.lit) | The isolated generic kernel identity above |
| [negative/expected.json](negative/expected.json) | Missing hypotheses, wrong carriers/arity/target group and false values |

These source results add no trust, native rule, operation alias or compiler
implementation. Quotient groups and the isomorphism theorems remain separate
work. A normal image in the whole target keeps its surjectivity hypothesis.
