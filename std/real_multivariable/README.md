# Real Euclidean coordinates

Ordinary finite real functions provide vectors and coordinate paths. This source
library adds seven templates, two propositions and ten checked theorems.

Configure the standard library import:

```ini
[import std]
vectors = real_multivariable
```

For example, replace the second coordinate of `(1,2)` with `7`:

```litex
release thm vectors:::real_coordinate_path_selected_component(2,(1,2),2,7)
release thm vectors:::real_coordinate_path_other_component(2,(1,2),2,1,7)
\vectors:::real_coordinate_path<2>((1,2),2,7)(1)=1
\vectors:::real_coordinate_path<2>((1,2),2,7)(2)=7
```

The templates are `real_zero_vector`, `real_vector_add`, `real_vector_sub`,
`real_vector_scale`, `real_euclidean_distance`, `real_coordinate_path` and
`real_linear_path`, each parameterized by a positive dimension. Vectors inhabit
`cart_n(R,n)`, the exact function space `fn(k closed_range(1,n)) R`.
`real_coordinate_path(p,axis,t)` replaces a coordinate with its new value `t`;
`real_linear_path(p,v,t)` has components `p(k)+t*v(k)`.

The propositions `is_real_euclidean_interior` and
`is_real_euclidean_accumulation_point` have explicit Euclidean ball definitions.
Theorems cover component evaluation, coordinate replacement at the base point,
unchanged other coordinates, commutative addition, subtraction of a vector from
itself, and interior of the full real coordinate space.

Native limit and derivative predicates and selectors are available independently
of this import. Prove a candidate before using its selector; see the
[multivariable examples](../../examples/real_analysis/multivariable/main.lit).
