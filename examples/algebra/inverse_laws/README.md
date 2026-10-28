# Elementary group inverse laws

These examples use the inverse laws for arbitrary groups, including groups
whose multiplication is not commutative. The inverse of a product reverses
the order of its factors:

```litex
thm inverse_of_product:
    ? forall A nonempty_set,G &Algebra::group::Group<A>,a,b A:
        G.inv(G.mul(a,b)) = G.mul(G.inv(b),G.inv(a))
    release thm Algebra::group::inverse_product(A,G,a,b)
```

The library also proves that the identity is its own inverse, taking an
inverse twice returns the original element, and a right inverse is unique.
The equation `x*a=b` has the unique solution `x=b*inv(a)`. If two elements
commute, their inverses commute as well.

The [noncommutative example](noncommutative/main.lit) uses the existing
Heisenberg group. Its generators show that `inv(a)*inv(b)` can differ from
`inv(b)*inv(a)`. They also show why the solution of `x*a=b` has the order
`b*inv(a)`: the other order gives a different result.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | The laws and concrete values in the additive integer group |
| [trivial/main.lit](trivial/main.lit) | The laws in a one-point group |
| [noncommutative/main.lit](noncommutative/main.lit) | Order-sensitive products and equations in the Heisenberg group |
| [contracts/main.lit](contracts/main.lit) | The six generic signatures and their hypotheses |
| [readme/main.lit](readme/main.lit) | The generic inverse-product example above |
| [negative/expected.json](negative/expected.json) | Rejected false values, missing premises and invalid carriers |

These are elementary group results. Quotient groups and the isomorphism
theorems remain separate work.
