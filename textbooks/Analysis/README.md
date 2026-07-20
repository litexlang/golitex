# Tao Analysis I as one Litex project

The Analysis chapter files are one project, declared by
[`litex.config`](litex.config).
The manifest exports each chapter in source order; it does not itself assert
mathematical facts.

Run the project entrance with:

```text
target/debug/litex -r textbooks/Analysis
```

Run an individual registered chapter from the project directory with:

```text
(cd textbooks/Analysis && ../../target/debug/litex -f chapter10-differentiation.lit)
```

Earlier exports are loaded by the ordered manifest.  Later chapters refer to
their public source-facing interfaces by canonical name:

```text
chap9::has_function_limit(...)
chap10::cauchy_mean_value_theorem(...)
```

There is no local-import statement or unqualified import completion.  A
chapter-local definition remains bare; every earlier chapter definition keeps
its `chapN::` qualifier, so its identity is explicit even when another export
uses the same short name.

Some similarly named source definitions remain deliberately local.  In
particular, Chapter 7 uses a non-strict series-tail convention (`<= epsilon`)
where Chapter 6 uses a strict sequence-tail convention (`< epsilon`), and
Chapter 11's monotonicity predicates are non-strict whereas Chapter 9's are
strict.  These are not duplicate interfaces to erase.

## Chapter 6 concept-first surface

Chapter 6 separates the candidate-limit relation `$has_limit(a,L)` from the
existence property `$is_convergent_sequence(a)`, proves the named uniqueness
result `sequence_limit_unique`, and then exposes the selected value `lim(a)`
with `have fn ... by exist!`.  Limit laws such as `seq_add_converges_to`
consume `has_limit` directly; they are a sibling branch rather than a result
that depends on `lim`.

A representative use is:

```litex
forall a seq(R):
    $is_convergent_sequence(a)
    =>:
    $has_limit(a, lim(a))
```

The same chapter exposes real exponentiation through rational approximation.
`rational_power_approx_seq(x,q)` is the sequence `n |-> x^(q(n))`, and
`real_power_agrees_with_rational_power` verifies the rational case by proving
that the constant rational approximation has limit `x^q`:

```litex
by thm real_power_agrees_with_rational_power(x, q)
$has_limit(rational_power_approx_seq(x, fn(n N_pos) R {q}), x^q)
```

The corresponding human design map is in `math_collections.md`; the runtime
definition graph exposes the actual typed dependencies retained by an
executed project environment.  Its current default-project artifact honestly
marks Chapter 6 as a trusted/affect-only project export.  Strict verification
is presently blocked by an earlier Chapter 5 trust boundary, so skipped proof
bodies are not represented as if they had been checked.

## Chapter 11 integration surface

Chapter 11 follows the dependency chain documented in
[`math_collections.md`](math_collections.md). Its central public interfaces
are the predicates `$is_partition_of_bounded_interval`,
`$is_finer_partition_than`, `$is_piecewise_constant_on`, and
`$is_riemann_integrable_on`; their corresponding construction and value APIs
are `interval_length`, `common_refinement`,
`refinement_fiber`, `refinement_owner`, `refinement_fiber_sum`,
`piecewise_constant_integral_with_partition`,
`piecewise_constant_integral`, `upper_riemann_sum`, `lower_riemann_sum`,
`upper_riemann_integral`, `lower_riemann_integral`, and `integral_on`. The
Stieltjes layer mirrors the last three with `upper_riemann_stieltjes_integral`,
`lower_riemann_stieltjes_integral`, and `stieltjes_integral_on`; its interval
weight is `alpha_interval_length`. The relational specification
`$has_alpha_interval_length` and its theorem
`alpha_interval_length_has_value` are the stable bridge from that value to its
endpoint cases.

The final Chapter 11 layer keeps the same distinction: the integral function
from a left endpoint is the value API `integral_from_left_endpoint`, while
`$is_antiderivative_of`, `$maps_closed_interval_to_closed_interval`, and
`$is_composition_on_closed_interval` are assumptions about displayed
functions. FTC, integration by parts, and change of variables are theorems.
The left-endpoint selector has one narrow, visible trust boundary because its
restriction function has a domain that changes with `x`; its stable
specification bridge is `$has_integral_from_left_endpoint` together with
`integral_from_left_endpoint_has_value`. The canonical function satisfies the
relational global predicate by
`selected_left_endpoint_integral_is_integral_function`.

The checked finite-regrouping bridge consists of
`$is_refinement_fiber`, `refinement_fiber`, and
`refinement_fiber_partitions_coarse_piece`: it identifies the nonempty fine pieces
inside a coarse piece and proves that they partition that coarse piece. Empty
fine pieces are deliberately excluded, since they do not have a unique coarse
owner and their later contributions vanish. Conversely,
`nonempty_fine_piece_has_unique_coarse_piece` and `refinement_owner` give every
nonempty fine piece its unique coarse owner. The checked
`refinement_owner_is_in_refinement_fiber` and
`refinement_fiber_member_has_owner` make those two descriptions mutually
usable: membership in a fiber and ownership by its coarse piece agree.
`nonempty_refinement_support` removes the ownerless empty pieces, and
`refinement_fiber_family_is_finite_unique_cover` supplies the corresponding
finite unique-cover instance for generic regrouping.
The checked
`refinement_fiber_has_finite_representative` bridge supplies the finite carrier
needed by the selected inner value `refinement_fiber_sum`. The
remaining outer/inner finite-sum reindexing equality is explicit proof debt;
it is not represented by a trusted numerical API. Its intended reusable shape
is `$is_finite_indexed_subfamily`, `$has_indexed_fiber_sum`, and
`$is_finite_unique_cover_of`, followed by a finite-sum reindexing theorem.
The first three form a checked relation-first core: a caller supplies an outer
summand and proves each of its values is the sum on the displayed fiber. The
weight is defined on the common carrier of real subsets, so deleting one index
changes the summation family but not the weight itself. The checked theorems
`finite_set_sum_over_singleton_unique_cover`,
`finite_unique_cover_distinct_fibers_are_disjoint`,
`finite_unique_cover_residual_after_removing_index`, and
`indexed_fiber_sum_persists_after_removing_index` supply respectively the
singleton base, disjointness, residual-cover, and residual-summand steps for
the finite induction. The remaining generic unique-cover equality is still
proof debt; it must be a reusable finite-combinatorics theorem, not a trusted
Chapter-11 numerical API.

For example, once `P` and `Q` have been shown to partition `I`, derive their
carrier facts and use the selected refinement directly:

```litex
by thm partition_is_set_of_real_subsets(I, P)
by thm partition_is_set_of_real_subsets(I, Q)
have Rf finite_set = common_refinement(I, P, Q)
$is_common_refinement_of_partitions(I, P, Q, Rf)
by thm common_refinement_is_partition_and_finer(I, P, Q, Rf)
```

For a fixed partition, the upper and lower sums are likewise callable values.
Their `*_has_value` theorems are the stable imported-module bridge from a
selector back to its relational specification:

```litex
have U R = upper_riemann_sum(I, P, f)
by thm upper_riemann_sum_has_value(I, P, f)
$has_upper_riemann_sum(I, P, f, U)
```

The selected step-integral and ordinary/Stieltjes integral values are
verified interfaces. Their remaining `trust` is limited to the source-facing
finite-regrouping and approximation theorems recorded in
`scripts/Analysis/todo/03_integration_and_language_blockers.md`.

The Stieltjes piecewise-constant base currently remains the explicit relation
`$has_piecewise_constant_riemann_stieltjes_integral`. Its future selected value
depends on the same generic finite regrouping theorem, so the chapter does not
add a redundant trusted selector merely to make the API look symmetric.
