# Real Euclidean coordinates

Ordinary finite real functions provide vectors and coordinate paths. This source
library's main export adds seven templates, two propositions and ten checked
theorems. Its directional export adds two templates, two propositions and nine
checked source theorems.

The `cross_product` export adds one ordinary function and fifteen proved source
theorems for real three-dimensional cross products. It adds no native operator
or builtin theorem.

Configure the standard library import:

```ini
[import std]
vectors = real_multivariable
```

For example, replace the second coordinate of `(1,2)` with `7`:

```litex
release thm vectors::main::real_coordinate_path_selected_component(2,(1,2),2,7)
release thm vectors::main::real_coordinate_path_other_component(2,(1,2),2,1,7)
\vectors::main::real_coordinate_path<2>((1,2),2,7)(1)=1
\vectors::main::real_coordinate_path<2>((1,2),2,7)(2)=7
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

The `iterated_integrals` export implements ordered rectangular real iterated
integrals in source: five templates, six propositions and twenty-two proved
theorems. `iterated_integral_y_then_x<a,b,c,d>(f)` integrates y on [c,d], then
x on [a,b]. `iterated_integral_x_then_y<a,b,c,d>(f)` fixes the opposite order.
Each name has four template parameters and one ordinary function argument.
Require a<=b and c<=d; equal endpoints are supported. The actual function domain
is `real_closed_rectangle<a,b,c,d>`, a subset of cart_n(R,2).

`has_y_section_integrals(a,b,c,d,f,g)` supplies the integral of every y-section
as g(x); the x-section proposition is separate. The corresponding
`has_iterated_integral_y_then_x(a,b,c,d,f,L)` means that some such profile g
has outer Riemann integral L. `is_iterated_integrable_y_then_x` asserts existence
of L. The opposite order has its own candidate/existence propositions. Prove
the candidate, release the integrable theorem, then the value theorem:

```litex
have fn constant_rectangle(p \vectors::iterated_integrals::real_closed_rectangle<0,1,0,2>) R=7
release thm vectors::iterated_integrals::iterated_integral_y_then_x_constant(0,1,0,2,constant_rectangle,7)
release thm vectors::iterated_integrals::iterated_integral_y_then_x_integrable(0,1,0,2,constant_rectangle,14)
release thm vectors::iterated_integrals::iterated_integral_y_then_x_value(0,1,0,2,constant_rectangle,14)
\vectors::iterated_integrals::iterated_integral_y_then_x<0,1,0,2>(constant_rectangle)=14
```

Section and profile functions use the native sorted-interval domain spelling
`'[min(a,b),max(a,b)]` and `'[min(c,d),max(c,d)]`. Retain the explicit interval
coverage and rectangle-membership steps in the
[product example](../../examples/real_analysis/multivariable/iterated_integrals/main.lit).
For a coordinate formula, that example declares the exact restriction with
`p cart_n(R,2): p $in rectangle`, then checks its membership in the rectangle
function space. A full-space function must be restricted explicitly.

The source proves section/value uniqueness, unique selection, constants,
addition and scalar multiplication for each order. It adds no native BT,
automatic integration rule, source trust or axiom. The two product orders are
proved independently. Independent multidimensional Riemann integration,
automatic order exchange, Fubini, arbitrary regions and variable bounds are
outside this export.

For a right-handed cross product u×v, use
`vectors::cross_product::real_cross_product(u,v)`. Both inputs and the output
belong to `cart_n(R,3)`, equivalently the complete function space
`fn(k closed_range(1,3)) R`. The formula is
`(u(2)*v(3)-u(3)*v(2),u(3)*v(1)-u(1)*v(3),u(1)*v(2)-u(2)*v(1))`.
Zero vectors are valid. This is a total source function; it does not require
a candidate/existence predicate, normalize its inputs or reuse the name `curl`.

Release its ordinary definition with
`release obj def vectors::cross_product::real_cross_product` when unfolding it
in an imported caller. `real_cross_product_components(u,v)` exposes all three
coordinate equations. `real_cross_product_value(u,v,a,b,c)` proves equality to
`(a,b,c)` from the three scalar coordinate calculations. Concrete calculations
may need the input coordinate equations first; the
[complete example](../../examples/real_analysis/multivariable/cross_product/main.lit)
shows those steps without relying on the existing mixed-tuple release gap.

The source theorems prove self/zero products, anticommutativity, left/right
addition and scalar multiplication, perpendicularity to both inputs, the
Lagrange and Euclidean norm-square identities, and the vector triple-product
formula u×(v×w)=〈u,w〉v−〈u,v〉w. `real_inner_product_three(u,v)` supplies the
existing real inner product's three-coordinate expansion.
`real_cross_product_scalar_triple(u,v,w,A)` proves
`inner_product(u,real_cross_product(v,w),3)=det(A,3)` when the real 3×3 matrix A
has columns u,v,w; these column equations are explicit premises.
All theorem names above are in `vectors::cross_product`.
The export has no trust or axioms. Cross products over C, arbitrary dimensions
and associativity are not supplied. Ordinary JSON/source proof mechanisms are
reused; no dedicated cross-product LaTeX notation or Lean replay is claimed.

The `higher_order` export defines ordered finite partial derivatives in source.
A function takes one vector input; a path in
`finite_seq(closed_range(1,n),k)` specifies the first-to-last coordinate order.
The same complete `fn(j closed_range(1,k)) closed_range(1,n)` is accepted.
Order zero is point evaluation and accepts `tuple()` or a complete empty function.

The candidate is
`has_ordered_partial_at(n,D,k,f,p,indices,L)`. Its certificate supplies actual
nested domains and intermediate functions. Each derivative step uses the native
two-sided coordinate definition on that intermediate function's actual domain.
The proposition `is_ordered_partially_differentiable_at(n,D,k,f,p,indices)`
asserts existence along this specified path. The source selector has three
template parameters and three ordinary arguments:

```litex
\vectors::higher_order::ordered_partial<n,D,k>(f,p,indices)
```

Prove the candidate, release `ordered_partial_candidate_exists`, then release
`ordered_partial_value` before using the selected value in a calculation.
`ordered_partial_from_global_profiles` is a convenience theorem for a supplied
zero-based finite family on the whole space, after proving every derivative step.
It does not infer the family or differentiate in WD. Native one- and two-step
bridges retain local domains. Paths are never sorted or exchanged automatically.
See the [ordered higher-partial example](../../examples/real_analysis/multivariable/higher_order/main.lit).

The independent `unary_higher_order` export handles `f^(k)(p)` for a unary real
function on its actual domain D. It uses `NthDerivativeProfiles<k>` with nested
real regions, the candidate `has_nth_derivative_at(D,k,f,p,L)`, and the existence
property `is_n_times_differentiable_at(D,k,f,p)`. Its selector is
`\vectors::unary_higher_order::nth_derivative<D,k>(f,p)`, with exactly two
template parameters and two ordinary arguments. Prove a candidate, then release
`nth_derivative_candidate_exists` and `nth_derivative_value`. Order zero returns
f(p); the native first derivative and one-step candidate have both source
bridges. `nth_derivative_from_global_profiles` accepts supplied full-real
functions after the native derivative of each preceding function is proved.
It does not identify real inputs with one-dimensional vectors.

Both higher-order exports prove uniqueness by induction for arbitrary finite
natural orders. They add no native Obj/Fact, reserved BT, automatic higher-order
derivative strategy, source axiom or trust. Smoothness classes, exchange of mixed
partials, alpha-count selectors and higher total multilinear derivatives remain
outside these exports.

`higher_order::ordered_partial_prefix_exists` proves existence for a supplied
coordinate prefix of an already proved ordered candidate. Its parameters are
`(n,D,k,m,f,p,indices,prefix,L)`, where 0<=m<=k and the prefix agrees with indices
at each of its positions. `unary_higher_order::nth_derivative_lower_order_exists`
has parameters `(D,k,m,f,p,L)` and derives the mth-order existence property from
the supplied kth-order candidate. Both retain the actual nested domains. These
are explicit source theorems; selector WD does not run them automatically.


The valued restriction theorems `ordered_partial_prefix_candidate/9` and
`nth_derivative_lower_candidate/6` take a supplied certificate and expose its
intermediate value as a candidate. The old existence-only theorems reuse them.
`ordered_partial_from_profiles_on/6` and `nth_derivative_from_profiles_on/4`
accept supplied families on any common actual domain D; the existing global
convenience interfaces reuse these proofs.

The all-point existence props are
`is_ordered_partially_differentiable_on(n,D,k,f,E,indices)` and
`is_n_times_differentiable_on(D,k,f,E)`, where E⊆D. They guard the ordinary
returned functions `ordered_partial_function<n,D,E,k>(f,indices)` (4+2) and
`nth_derivative_function<D,E,k>(f)` (3+1), respectively. The actual returned
domain is exactly E, including at order zero. Their `_selected` and `_value`
theorems preserve the original candidate/existence/selection boundary.

`ordered_partial_chain_region_in_domain/7` and
`nth_derivative_chain_region_in_domain/5` expose that a certificate's region is
a subset of D. `ordered_partial_chain_exists_on/9` and
`nth_derivative_chain_exists_on/6` derive the matching all-point existence prop.
`ordered_partial_function_successor/10` and
`nth_derivative_function_successor/7` then prove the native next derivative of
the selected prefix function on that actual preceding region. They consume a
supplied chain and the matching on prop; they do not synthesize a chain in WD.
The [unary coherence example](../../examples/real_analysis/higher_derivatives/coherence.lit)
constructs first and second derivative functions on the actual witness regions.
The successor theorems accept the current order m and a length-m prefix, then
produce the (m+1)st candidate. This avoids asking a caller to treat a length-1
path as a separately instantiated `finite_seq(...,2-1)`. The examples make the
remaining ordinary region/value index equalities explicit.
