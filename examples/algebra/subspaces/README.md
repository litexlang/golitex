# Inherited finite-dimensional subspaces

This consumer imports std algebra and reuses the real-plane model in
[dimension_extension/model.lit](../dimension_extension/model.lit). It does not
redeclare Field or VectorSpace and introduces no trust or axiom.

[main.lit](main.lit) checks the x-axis with its actual inherited operations,
constructs the one-vector basis (e1), proves dimension 1, and compares it with
ambient dimension 2. The whole inherited plane and the inherited singleton zero
space have dimensions 2 and 0. It then checks the linear projection T(x,y)=(x,0),
e2 in the kernel and e1 in the image, and uses the new subspace interfaces to
obtain finite-dimensional kernel/image spaces and their ambient upper bound.
These last checks do not establish rank-nullity or compute both projection
subspace dimensions as 1.

The guarded constructions are
`\Algebra::subspace::restricted_space<K,F,V,X,U>`,
`\Algebra::subspace::restricted_add<K,F,V,X,U>`,
`\Algebra::subspace::restricted_smul<K,F,V,X,U>` and
`\Algebra::subspace::inclusion<V,U>`.
First prove is_subspace, call subspace_is_nonempty, and obtain the constructor's
carrier with restricted_space_is_vector_space. Prove inherited finite dimension
before applying the existing finite_dimension<K,F,U>(inherited_space) selector.
The dimension-bound theorem has both finite-dimensional domains explicitly.

The source proof compares canonical template expressions. An ordinary typed
alias of the inherited struct is also tested as the argument of finite_dimension.
A direct span-template equality through an equal struct alias is a separately
recorded rejected diagnostic; the successful proof uses canonical arguments.

[contracts.lit](contracts.lit) has 19 statements: three carrier preconditions,
twelve named forwarding consumers, and four value-carrier contracts. Together
these exercise all thirteen new exported source theorem names and four source
value families. They are generic over the supplied field and space.

Run:

```sh
python3 examples/algebra/subspaces/check.py
```

Use `--binary /path/to/litex` for a fixed release binary. The checker performs
18 strict CLI checks: source, imported main, generic contracts, thirteen
last-statement rejection controls, and two real installed layouts without a
std path override. It also compares the complete current std/WiX file inventory.

Controls refuse absent ambient finiteness or independence, absent subspace
proofs, absent inherited finiteness, a reversed sequence inclusion, an illegal
inclusion argument, unequal combination values, a dimension above the ambient
one, axis dimension 2 and positive zero-space dimension. Each expected failure
must leave all earlier statements accepted, and its exact rejection phase is
checked. Parse rejection does not count as mathematical boundary evidence.

The named projection_axis_facts theorem exports the five previously proved
projection/axis facts for the rank_nullity consumer. It adds no new fixture
assumption or definition; that consumer now computes both dimensions as 1.
