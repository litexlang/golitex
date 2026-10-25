# Real Euclidean coordinates

Ordinary finite real functions provide vectors and coordinate paths. This source
library's main export adds seven templates, two propositions and ten checked
theorems. Its directional export adds two templates, two propositions and nine
checked source theorems.

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

For a directional derivative D_v f(p), use the `vectors::directional` export.
The first version requires n positive and a scalar f on all of cart_n(R,n).
The supplied v retains its length and may be zero. There is no implicit unit
normalization. `directional_section<n>(f,p,v)` is t ↦ f(p+t v).

The candidate prop is `has_directional_derivative_at(n,f,p,v,L)`; the property
`is_directionally_differentiable_at(n,f,p,v)` means that this one section is
differentiable at zero. Neither implies total differentiability. The source
selector `directional_derivative_at<n>(f,p,v)` reuses the native unary derivative
and requires native `is_differentiable_at(section,0)` as its exact guard.

After proving a candidate, explicitly release `directional_candidate_differentiable`
before the value theorem or selector, including in an imported caller. WD checks
the selected expression before running the value theorem body. For example:

```litex
have fn bowl(x cart_n(R,2)) R=x(1)^2+x(2)^2
$is_multi_differentiable_at(bowl,(1,2),2)
$has_gradient_at(bowl,(1,2),2,(2,4))
release thm vectors::directional::directional_from_gradient(2,bowl,(1,2),(3,-1),(2,4))
inner_product((2,4),(3,-1),2)=2
$vectors::directional::has_directional_derivative_at(2,bowl,(1,2),(3,-1),2)
release thm vectors::directional::directional_candidate_differentiable(2,bowl,(1,2),(3,-1),2)
release thm vectors::directional::directional_derivative_value(2,bowl,(1,2),(3,-1),2)
\vectors::directional::directional_derivative_at<2>(bowl,(1,2),(3,-1))=2
```

`directional_from_differential` proves the candidate from the supplied 1×n full
differential. `directional_from_gradient` requires both a gradient candidate
and full differentiability. These checked source wrappers invoke the two native
BTs `scalar_differential_along_line` and `differentiable_gradient_along_line`.
The remaining source results expose the section formula, uniqueness, candidate
to native differentiability, candidate to the directional property, the reverse
property bridge, candidate value, and a selected-value candidate.
There are no source axioms or trust statements. Restricted domains, vector-valued
directional derivatives and general higher orders remain outside this export.
See the [directional examples](../../examples/real_analysis/multivariable/directional/main.lit).
