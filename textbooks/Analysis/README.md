# Tao Analysis I as one Litex project

The Analysis chapter files are one project, declared by
[`litex.config`](litex.config).
The manifest exports each chapter in source order; it does not itself assert
mathematical facts.

Run the project entrance with:

```text
target/release/litex -r textbooks/Analysis
```

Run an individual registered chapter from the project directory with:

```text
(cd textbooks/Analysis && ../../target/release/litex -f chapter10-differentiation.lit)
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

Some similarly named source definitions remain deliberately local. In
particular, Chapter 7 uses a non-strict series-tail convention (`<= epsilon`)
where Chapter 6 uses a strict sequence-tail convention (`< epsilon`).

## Chapter 3 cardinality surface

Chapter 3 defines equal cardinality through a bijection and proves the
Cantor-Schroeder-Bernstein theorem as `cantor_schroeder_bernstein`: injections
in both directions produce a bijection.  The proof iterates `g(f(x))` from the
part of the first set outside `g`'s range, uses `f` on the resulting reachable
region, and uses the unique inverse of `g` on its complement.  Later chapters
can call it as `chap3::cantor_schroeder_bernstein` without importing a separate
cardinality module or assuming any form of choice.

The same chapter proves `chap3::subset_of_finite_set_is_finite`. It expresses
a subset as a double set difference inside its finite ambient set, so Chapter
8 can reuse the checked result without importing `std`.

## Chapter 4 formal-difference surface

Chapter 4 represents Tao's formal difference `a-b` by the pair `(a,b)` in
`formal_difference = cart(N,N)`. The predicate
`$represent_same_integer(p,q)` is the cross-sum relation
`p[1]+q[2]=q[1]+p[2]`; it does not use Litex's truncated subtraction on `N`.
The callable constructions `add_formal_differences`,
`multiply_formal_differences`, and `negate_formal_difference` implement the
representative formulas. Their preservation of `represent_same_integer` is
proved by the three corresponding well-definedness theorems before the chapter
switches to builtin `Z` and `Q` arithmetic.

A representative checked use is:

```litex
by def $represent_same_integer((3, 1), (4, 2))
```

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
executed project environment.  The Chapter 5 identification between builtin
`R` and the rational-Cauchy construction is stated explicitly through the
axioms `cauchy_sequence_representative_in_Q_exists` and
`real_cauchy_sequence_has_limit_in_R`; these are foundational compatibility
assumptions, not unfinished Chapter 5 proofs.

## Chapter 8 infinite-set interface

Chapter 8 builds on Chapter 3's bijection and finite-cardinality interfaces.
Its first layer exposes `$embeds_into`, `$is_countably_infinite`,
`$is_at_most_countable`, and `$is_uncountable`, together with closure under
subsets, images, binary unions, and Cartesian products. The source-facing
`union_of_two_countable_sets_is_countable` now verifies by an even/odd
interleaving, followed by the at-most-countable and infinite bridges.
`integers_are_countable` enumerates the range of `n |-> -n`, proves
`Z = N union (-N)`, and then applies that union theorem. The later product and
rational-countability proofs reuse these named results.  The countable-family
union theorem also verifies: it uses the explicit choice axiom to select one
injective coding graph per fiber and pairs the outer and inner natural codes.

The next layer represents countable-set sums by composing a displayed
enumeration with the summand, then relates finite absolute subsum bounds to
sums over arbitrary supports. Chapter 8 also provides Cantor's theorem,
function-valued infinite Cartesian products, explicit choice-axiom
interfaces, partial/total/well-order predicates, strong induction, and Zorn's
maximal-element principle. The detailed concept roles and dependency order
are recorded in [`math_collections.md`](math_collections.md).

Proof boundaries remain visible. Finite subsum comparison and capture,
coordinate-swap transport, nonzero-support countability, scalar
multiplication, bijection change of variables, finite-total-order
well-ordering, enumeration independence for absolutely convergent
countable-set sums, and both the nonnegative and signed row-first Fubini
arguments are checked.
Bijection change treats finite support by finite
substitution and countably infinite support by transported enumeration.  The
row-first argument constructs the row sums, proves the
finite-row series law by induction, and compares arbitrary finite supports
with finite rectangles.  The signed argument applies that result to positive
and negative parts and recombines the row sums.  The strict enumerated series
predicates still describe countably infinite carriers, while the
at-most-countable interface has a finite-sum branch and an enumerated branch.
Lemma 8.2.3 is checked in both directions, and arbitrary-set sums use the
repaired interface on their nonzero support.  Zero extension and reflection
transport values between an at-most-countable support and a larger common
carrier; addition applies the Chapter 7 law on that common carrier and then
removes terms cancelled to zero.  The disjoint-union law zero-extends both
restricted families to the union, applies addition, and uses disjointness
pointwise.  The scalar law, including the zero-scalar empty-support branch,
is checked.  The binary-decimal map is selected from a
proved unique series sum, and its injectivity is checked using the first
differing digit and a geometric-tail bound.  The remaining Chapter 8 `trust`
is concentrated in the conditional-sign and Riemann rearrangement exercises
and four good-chain lemmas.  The axiom of choice remains an
explicit `axiom`; checked callers do not erase that provenance.

## Chapter 10 differentiation interface

Chapter 10 keeps a candidate derivative, its existence predicate, and its
selected value distinct: `$has_derivative_at(X,f,x,L)`,
`$is_differentiable_at(X,f,x)`, and `derivative(X,f,x)`.  At function level,
`$is_differentiable_on(X,f)` and `$has_derivative_function_on(X,f,df)` quantify
only over Chapter 9 limit points.  `derivative_function(X,f)` is the partial
function on the differentiability locus, so it does not manufacture values at
isolated or nondifferentiable points.  Corollary 10.1.12 combines derivative
continuity at limit points with the elementary fact that every function is
continuous at an isolated domain point.

The Chapter 10 inverse-derivative theorems use
`chap9::is_inverse_pair_on` directly.  Its inverse has codomain `X`, while
Litex still permits it wherever the analysis interface accepts a real-valued
function.  The inverse function theorem is fully checked: its proof composes
the inverse with the reciprocal of the forward difference quotient on the
exact nonzero subtype.

The two directions of Proposition 10.1.7 are exposed as reusable theorems,
and the source equivalence between derivatives and Newton approximations is
also stated directly.  In Section 10.5, `lhopital_rule_first` returns one
punctured radius together with the quotient limit on that same local carrier.
`lhopital_rule_second` is the complete right-hand theorem: it returns both
denominator nonvanishing on `(a,b]` and the quotient limit.

