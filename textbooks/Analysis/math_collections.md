# Mathematical Collections for Tao Analysis I

## Concept-card convention

For each central mathematical concept, record its ordinary meaning, semantic
role, ideal Litex form, representative interface, nearest rejected form,
direct dependencies, one downstream use, and any honest proof or language
boundary.  These are separate questions: a concept can be a function while
its current unique-existence proof is trusted, or a property while every
theorem about it is checked.  Knowledge state never changes the mathematical
role of the concept.

## Book-wide struct boundary

A `struct` is appropriate when the mathematics carries several named data
fields together and later arguments repeatedly project those fields.  Nested
structs are therefore a natural interface for genuine structure extension,
such as a vector space containing its scalar system. They are not a blanket
replacement for Analysis I's relations, witnesses, functions, or selected
values. Candidate limits, convergence, derivative relations, and continuity
remain `prop` interfaces; `lim` and `derivative` remain callable selected
values.

The closest Analysis I pilot is the recursive bisection state in Chapter 5.
Its ordinary meaning is a lower and upper real endpoint satisfying the shared
bracketing laws.  The ideal packaged interface is:

~~~litex
struct BisectionState<E set>:
    lower R
    upper R
    <=>:
        not $is_upper_bound(E, lower)
        $is_upper_bound(E, upper)
        lower <= upper
~~~

This is a structure rather than a replacement predicate: a caller should be
able to bind `state &BisectionState<E>` and read `state.lower` and
`state.upper`, while a candidate-state relation may still be useful before
packaging.  A verified nested use can place such a value in another struct and
read `process.initial.lower`.  The current source nevertheless keeps its
checked pair-valued recursive sequence.  Field shorthand does not continue
after a function call, so a state sequence requires the longer expression
`&BisectionState<E>{states(n)}.lower`; migrating the existing `pair(n)[1]`
proofs now would increase, rather than reduce, the public proof surface.

Chapter 4 formal differences are a smaller named-field possibility, but the
mathematical identity of that section is the equivalence relation on displayed
representatives.  Named fields must never replace `represent_same_integer` or
hide quotient well-definedness.  Chapter 8 order notions primarily add laws to
one displayed relation and have no repeated nested field consumers in this
book, so their current `prop` interfaces remain the right surface.

The resulting dependency and migration order is:

~~~text
new struct/object-system semantics
  --compatibility--> ordered Chapters 1--10
  --use probe--> BisectionState<E>
  --nested field probe--> a process containing BisectionState<E>
  --language boundary--> explicit view after states(n)

formal differences --possible named data--> representative operations
                  --required relation--> represent_same_integer
~~~

Compatibility comes first.  A future struct migration should begin with one
owner chapter only after its field projections make the checked proofs shorter
in real caller context.  Do not preserve both tuple and struct surfaces through
aliases or trusted wrappers, and update this design before changing a core
interface.

## Chapter 4: formal differences

Tao's construction of the integers starts from ordered pairs of natural
numbers. The pair `(a,b)` denotes the formal difference `a-b`; two pairs
denote the same integer when their cross sums agree. Because Litex subtraction
on `N` is truncated, this construction must not be encoded by the ordinary
expression `a - b`: for example, `0 - 1` and `0 - 2` are both `0`, although
the corresponding formal differences are not equivalent.

The carrier is `formal_difference = cart(N,N)`, and equality of represented
integers is the relation

~~~litex
prop represent_same_integer(p, q cart(N, N)):
    p[1] + q[2] = q[1] + p[2]
~~~

This is a `prop`, not a function returning an integer, because quotient
identification is a relation on two displayed representatives. The nearest
rejected form is `p[1] - p[2] = q[1] - q[2]` over `N`; truncated subtraction
collapses distinct negative formal differences.

Addition, multiplication, and negation are representative-level constructions
and therefore are `have fn` interfaces:

~~~litex
have fn add_formal_differences(p, q cart(N,N)) cart(N,N) =
    (p[1] + q[1], p[2] + q[2])

have fn multiply_formal_differences(p, q cart(N,N)) cart(N,N) =
    (p[1] * q[1] + p[2] * q[2], p[1] * q[2] + p[2] * q[1])

have fn negate_formal_difference(p cart(N,N)) cart(N,N) = (p[2], p[1])
~~~

The well-definedness theorems prove that each construction preserves
`represent_same_integer`; these proofs are the dependency boundary needed
before the formulas can be regarded as operations on equivalence classes.
The chapter then uses Litex's builtin `Z` for later integer arithmetic. No
unchecked identification between the quotient and builtin `Z` is introduced.

## Chapter 6: sequence limits

The sequence-limit API illustrates the intended concept-first order.  First
introduce the carrier and the candidate-limit relation, then convergence and
uniqueness, and only then select the canonical limit value.

### Real sequences

`seq(R)` is the builtin parameterized family of positive-natural-indexed real
sequences.  It is a carrier family, not a proposition and not a user template.
A caller uses a sequence as a function, for example `a(n)`.

### Candidate limit and convergence

~~~litex
prop has_limit(a seq(R), L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)

prop is_convergent_sequence(a seq(R)):
    exist L R st {$has_limit(a, L)}
~~~

`has_limit(a,L)` is a relation on a proposed value, while
`is_convergent_sequence(a)` is an existence property.  Both are props because
later mathematics asserts them.  Reject a function-only definition at this
stage: uniqueness has not yet selected a value, and proofs still need to state
that a supplied `L` is a limit.

The definition dependency is
`has_eventual_closeness_to -> has_limit -> is_convergent_sequence`.  A minimal
use is `$has_limit(a,L)` under an epsilon-tail proof; a convergence proof may
instead provide `exist L R st {$has_limit(a,L)}`.

### Uniqueness and the selected limit

~~~litex
thm sequence_limit_unique:
    ? forall a seq(R), L1, L2 R:
        $has_limit(a, L1)
        $has_limit(a, L2)
        =>:
            L1 = L2

have fn lim by exist!:
    ? forall a seq(R):
        $is_convergent_sequence(a)
        =>:
            exist! L R st {$has_limit(a, L)}
~~~

`sequence_limit_unique` is a named reusable fact.  `lim` is a canonical
selection because downstream mathematics must write `lim(a)`; leaving only a
three-argument limit relation would force every limit law to carry an
unnecessary witness.  Its existence dependency is convergence, its uniqueness
dependency is `sequence_limit_unique`, and the selected value is related back
to the specification by `$has_limit(a,lim(a))`.

### Limit laws

~~~litex
thm seq_add_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit(fn(i N+) R {a(i) + b(i)}, x + y)
~~~

Limit laws are theorems consuming the earlier relation and function
interfaces.  They must not be folded into the definition of convergence or
`lim`.  The representative source progression is not one dependency chain;
its typed DAG has this shape:

~~~text
seq(R) --signature--> has_limit
has_eventual_closeness_to --definition--> has_limit
has_limit --definition--> is_convergent_sequence
has_limit --statement/proof--> sequence_limit_unique
is_convergent_sequence --well-definedness--> lim certificate
has_limit --specification--> lim certificate
sequence_limit_unique --proof--> lim certificate --selection--> lim
has_limit --statement/proof--> seq_add_converges_to and the other limit laws
~~~

In particular, the limit-addition theorem does not depend on the selected
function `lim`; both are downstream consumers of the candidate-limit relation.
The chapter source currently contains all of these interfaces.

### Real powers from rational approximations

`rational_power_approx_seq(x,q)` is the sequence `n |-> x^(q(n))`, while
`is_rational_approximation_sequence(q,alpha)` is the condition that every
`q(n)` is rational and that `q` converges to `alpha`.  The first is a
`have fn` because later proofs apply the sequence; the second is a `prop`
because callers assert it about a displayed approximation.

For a rational exponent, agreement with the real-exponent construction is a
source-facing theorem about the constant rational approximation:

~~~litex
thm real_power_agrees_with_rational_power:
    ? forall x R+, q Q:
        $has_limit(rational_power_approx_seq(x, fn(n N+) R {q}), x^q)
~~~

This is a theorem rather than a new function or predicate: `x^q` is already
the callable power value, and the missing mathematical content is that the
constant approximation used by the real-exponent construction converges to
that value.  Reject the vacuous equality `x^q = x^q`; with the current power
notation it places the same expression on both sides and exposes no agreement
with the approximation construction.  The checked dependency route is
`constant_sequence_has_limit -> is_rational_approximation_sequence ->
rational_power_approx_seq_has_limit -> real_power_agrees_with_rational_power`.
One direct use is a theorem call followed by the displayed `has_limit` fact.

Definition Graph v0.2 reports the edges actually available in its execution
mode.  Chapter 5 states the identification between builtin `R` and the
rational-Cauchy construction through two explicit compatibility axioms rather
than unfinished theorem proofs.  Generated artifacts should preserve that
axiom provenance.  The proof edges above remain part of this human contract
when an execution mode does not expose the checked bodies that establish them.

## Chapter 8: infinite sets

Chapter 8 has one mathematical spine rather than five unrelated collections
of declarations. Chapter 3 supplies bijections, injections, finite
cardinality, and Cantor--Schroeder--Bernstein. Section 8.1 turns these into a
usable countability calculus. Section 8.2 uses countable enumerations to
define sums over sets. Section 8.3 separates countable from uncountable sets.
Section 8.4 makes the non-constructive selection principle explicit. Section
8.5 packages the order vocabulary needed for strong induction and Zorn's
lemma.

### Concept inventory

| Concept | Semantic role and Litex form | Main dependency and downstream use |
| --- | --- | --- |
| `embeds_into(S,T)` | Existence property, hence `prop` | An injective function `S -> T`; used to transfer at-most-countability and infinitude. |
| `is_countably_infinite(X)` | Cardinality property, hence `prop` | A Chapter 3 bijection `N -> X`; supplies an enumeration. |
| `is_at_most_countable(X)` | Existence property, hence `prop` | An injection `X -> N`; closed under subsets, images, and countable unions. |
| `is_uncountable(X)` | Cardinality property, hence `prop` | Infinite but not countably infinite; the checked bridge shows this excludes an injection into `N`. |
| Countable enumeration | Relation on a displayed function, hence `prop is_countable_enumeration` | A bijection `N+ -> X`; turns a set-indexed family into a Chapter 7 sequence. |
| Countable-set series terms | Formula-defined function, hence `template` plus `have fn` | Applies `f` after an enumeration; feeds Chapter 7 convergence and sum predicates. |
| At-most-countable convergence and sum | Finite/enumerated alternatives, hence paired `prop` interfaces | Finite carriers use `finite_set_sum`; countably infinite carriers use a bijection `N+ -> X`. |
| Absolute summability and set-series sum | Properties of a displayed family and candidate sum, hence `prop` | Finite absolute subsum bounds and countable support; used by Fubini and rearrangement results. |
| Infinite Cartesian product | Builtin set of choice functions | `general_cart(I,S,X)` has canonical builder form `{f ...: $is_choice_function_for(I,S,X,f)}`. |
| Choice function | Displayed function satisfying the builtin named `prop` `$is_choice_function_for` | Its definition is pointwise membership; the explicit choice axiom yields an existential whose body stays atomic. |
| Partial, total, and well order | Relations and properties, hence `prop` | Pair membership in an order relation; used by minima, induction, chains, and Zorn. |
| Minimal elements and upper bounds | Properties of displayed elements, hence `prop` | Order plus subset membership; used in strong induction and maximal-element arguments. |

These forms are deliberately not replaced by theorem-shaped wrappers. An
enumeration is a function witnessed by a bijection, not a predicate invented
for each particular set. A sum is represented by a candidate-value relation,
not by an unproved global choice of a numeric value. A partial order remains
a relation on a carrier rather than a record whose fields would have no later
projection-based use in this chapter.

### Countability dependency graph

The ideal dependency structure of Section 8.1 is:

~~~text
chap3::is_bijective_fn --definition--> is_countably_infinite
chap3::has_finite_cardinality --definition--> is_at_most_countable
subset_of_finite_set_is_finite --builtin theorem--> finite subfamilies in Chapter 8
is_at_most_countable --negation--> is_uncountable

is_at_most_countable + injective map --proof--> injection transfer
injection transfer --proof--> subset and image closure

two enumerations --construction--> even/odd interleaving
even/odd interleaving --image--> union is at most countable
enumeration of either input --embedding--> union is infinite
at most countable + infinite --proof--> union is countably infinite

N --negation map--> -N
N + -N --set equality--> Z --union theorem--> integers_are_countable
N x N --diagonal enumeration--> products --quotient map--> Q
~~~

This ordering is important. The bridge
`at_most_countable_with_N_embedding_is_countably_infinite` belongs before the
first closure theorem that needs it, even though a later example also uses it.
Proof-local constructions such as the even/odd interleaving function and the
enumeration of `-N` stay inside their source-facing theorems; they are not
chapter-level mathematical concepts.

Proposition 8.1.10 should follow its three mathematical steps:

1. Interleave bijections `N -> X` and `N -> Y` at even and odd indices.
2. Identify the resulting image with `X union Y`, obtaining at-most-countability.
3. Embed `N` through the enumeration of `X`, obtaining infinitude, and combine
   the two properties.

Corollary 8.1.11 should likewise remain a three-step proof: negate the natural
enumeration to enumerate `-N`, prove `Z = N union (-N)`, and call Proposition
8.1.10. The checked declarations are
`union_of_two_countable_sets_is_countable` and `integers_are_countable`.
Reject a global `is_negative_natural_part_member` predicate here: the negative
part is simply the range of the negation function, and the predicate obscures
the proof's actual nodes.

### Infinite sums and uncountability

Section 8.2 reuses the countability layer rather than creating a second notion
of enumeration:

~~~text
is_countable_enumeration
    --composition--> countable_set_series_terms
    --Chapter 7 series predicates--> countably-infinite convergence and sums
finite carrier --finite_set_sum--> finite-family convergence and sum
finite/enumerated alternatives --> at-most-countable convergence and sum
finite absolute subsum bounds
    --bounded nonnegative partial sums--> at-most-countable absolute convergence
    --support theorem--> at-most-countable nonzero support
    --finite/enumerated restriction--> arbitrary-set series sum
at-most-countable support sum
    --zero extension/reflection--> common-support sum
two common-support sums --Chapter 7 addition--> sum on the common support
common-support sum --remove cancelled zero terms--> sum on the nonzero support
two disjoint restricted sums --zero extension + addition--> sum on their union
double-index family --row/swap/column views--> Fubini interfaces
~~~

The checked support route now has two reusable intermediate nodes.  A
nonfinite set contains a finite subset of every prescribed natural size, and
the support is the countable union of the finite level sets
`{x : abs(f(x)) >= 1/n}`.  Bijection change of variables is also checked by
transporting both finite absolute subsums and the enumerated nonzero support.

The strict countable-series representation deliberately remains a bijection
`N+ -> X`, so it represents countably infinite carriers only.  The broader
interfaces `is_absolutely_convergent_at_most_countable_set_series` and
`has_at_most_countable_set_series_sum` add the mathematically separate finite
branch; the latter identifies the value with `finite_set_sum`.  Arbitrary-set
sums use this broader relation on their nonzero support.  Replacing bijectivity
with a repeating enumeration was rejected: it would count a finite term more
than once and would destroy the meaning of the series rather than model its
finite sum.

Zero extension is now a checked value-preserving operation on an at-most-
countable carrier.  Its finite branch is ordinary finite-sum deletion of zero
terms; its countably infinite branch handles both finite support and an
absolutely convergent enumerated support.  The reverse theorem obtains a sum
on the smaller carrier, extends it back, and uses uniqueness.  Consequently
the addition law uses the union of the two nonzero supports as one common
carrier, applies the Chapter 7 series-addition law there, and then reflects the
sum to the possibly smaller support left after cancellation.  The disjoint-
union law is the direct corollary: zero-extend each restricted family to the
union, add them, and use disjointness to identify the pointwise sum with the
original family.

The row, column, swapped, finite-bound, and finite-capture predicates are
relations on proposed witnesses. They make the proof route of Fubini visible;
they are not independently selected mathematical values. The templates for
positive and negative parts and nonzero support are parameterized
constructions used by later theorems.

Section 8.3 starts from the reusable checked theorem `cantor_theorem`: a set
cannot be equinumerous with its power set. Singleton embedding transfers this
to `power_set(N)`.  For `A : power_set(N)`, `binary_decimal_terms(A)` is the
ordinary Chapter 7 sequence whose positive index `k` carries
`(1/10)^(k-1)` when `k-1` belongs to `A`, and zero otherwise.  Thus
`has_binary_decimal_subset_sum(A,L)` is a candidate-value `prop`, defined by
`chap7::has_series_sum(binary_decimal_terms(A),L)`.  Comparison with the
geometric series proves existence, series-sum uniqueness proves uniqueness,
and only then does `binary_decimal_subset_sum` become a selected `have fn`.
Its injectivity is a theorem: at the least natural number where two subsets
differ, the leading contribution `(1/10)^n` is strictly larger than the whole
remaining geometric tail `(1/10)^n/9`.  Modeling the selected value directly
as an abstract property was rejected because it hid both the analytic
construction and the mathematical reason for injectivity.

~~~text
subset A of N
    --conditional decimal digits--> binary_decimal_terms(A)
    --geometric comparison--> has_binary_decimal_subset_sum(A,L)
    --series-sum uniqueness--> binary_decimal_subset_sum(A)
least differing digit + geometric tail bound
    --proof--> binary_decimal_subset_sum_is_injective
~~~

### Choice and order

For a family `X(alpha)` of subsets of one ambient carrier, membership in the
infinite product means exactly that a function chooses a value in every
factor. This quantified condition is named
`$is_choice_function_for(I,S,X,f)`; existential and set-builder bodies use the
atomic prop call, while `by def` exposes its pointwise `forall` when a proof
needs coordinates. The canonical builtin equality is
`general_cart(I,S,X) = {f fn(alpha I)big_union(S): $is_choice_function_for(I,S,X,f)}`.
`axiom_of_choice_for_subsets` is therefore an explicit axiom from a
nonempty-family property to existence of such a function. The finite-product
comparison theorems are checked representation results and do not depend on
that axiom. The generic `choice_property` is an external relation parameter
used only to state the pointwise-choice formulation; it must not become a
catch-all replacement for concrete source predicates.

Finite-set numbering uses the reserved theorem
`finite_set_has_bijective_index(X)`. Its witness carrier is
`finite_seq(X, finite_set_size(X))` and its atomic certificate is
`$bijective(closed_range(1, finite_set_size(X)), X, idx)`. The earlier
induction proof remains in Chapter 7 under the educational name
`finite_set_index_exists_by_induction`; consumers use the builtin interface.

The order layer is built in this order:

~~~text
partial order -> strict comparison -> total order on a subset
partial/total order -> minimal and maximal elements -> well ordering
well ordering + induction step -> strong induction
upper bound and strict upper bound -> chains
chains + explicit choice interface -> good-chain construction -> Zorn
~~~

The current honest boundaries are concentrated rather than hidden.  The
countable-union exercise and finite-total-order bridge are checked, as are
finite-subsum transport, support countability, coordinate swapping, scalar
multiplication, both finite and countably infinite branches of bijection
change, and zero-extension in both directions for arbitrary-set sums.  The
at-most-countable convergence and sum interfaces have explicit finite and
enumerated branches, so no statement is blocked merely because a support is
finite or empty.  Enumeration independence is checked by constructing the
permutation between two enumerations and applying absolute rearrangement plus
series-sum uniqueness.  Signed Fubini is checked by positive/negative-part
decomposition; arbitrary-set addition is checked on a common support; and the
binary-decimal selector and its least-differing-digit injectivity proof are
checked.  The disjoint support-series law is checked by zero-extending each
restriction to the union and applying arbitrary-set addition.  Riemann
rearrangement retains `trust`.  Choice itself is recorded as `axiom`.  The four
good-chain lemmas in the Zorn route also retain visible `trust`.  Checked final
theorems verify through these displayed dependencies without erasing trusted
or axiomatic provenance.

## Chapter 10: differentiation

This section is the Chapter 10 design map.  Its source of truth is Tao,
Analysis I, Sections 10.1--10.5, together with the source-facing declarations
in `chapter10-differentiation.lit`.  It records the intended mathematical
interfaces rather than claiming that every current proof or construction is
checked.  Examples, exercises, and proof-local auxiliary expressions are not
automatically public concepts.

### Modeling conventions

The ambient data are real subsets `X`, `Y`, points `x0`, `y0`, and displayed
functions such as `f : X -> R` and `g : Y -> R`.  They are ordinary parameters,
not templates.  Chapter 10 needs no bundled structure or field projection, so
it introduces no `struct`.  It also needs no `abstract_prop`: a proof gap does
not change whether a derivative is a relation, a value, or a function.

Use a `prop` when later mathematics asserts a relation or condition, a
`have fn` when it applies a formula-defined construction, and a
`have fn ... by exist!` only for a genuinely uniquely selected value.  A
`thm` is a named mathematical result, not a substitute for a missing object.
In particular, `trust` and `axiom` are proof statuses, never semantic roles.
The inverse-pair, composition, limit, continuity, extremum, and monotonicity
vocabulary that already belongs to Chapter 9 should be cited from `chap9`, not
redeclared under new Chapter 10 names.

### Concept inventory

| Source material | Semantic role | Ideal Litex form | Downstream use |
| --- | --- | --- | --- |
| Punctured difference quotient | Formula-defined function | `have fn` | State a derivative as a function limit and reuse the quotient in limit proofs. |
| `has_derivative_at(X,f,x0,L)` | Candidate-value relation | `prop` | State that a displayed real `L` is the derivative. |
| `is_differentiable_at(X,f,x0)` | Existence property | `prop` | Gate the selected point derivative. |
| `derivative(X,f,x0)` | Canonical value | `have fn ... by exist!` | Write `f'(x0)` as a real expression. |
| `is_differentiable_on(X,f)` | Domain property | `prop` | State differentiability at every limit point of a domain. |
| `has_derivative_function_on(X,f,df)` | Relation between displayed functions | `prop` | Let a theorem consume a supplied derivative function `df`. |
| `derivative_function(X,f)` | Formula-defined partial function | `have fn` | Apply the canonical derivative exactly at the differentiability points of `f`. |
| Newton approximation | Candidate linearization relation | `prop` | Give the first-order estimate used by continuity and the chain rule. |
| Local maximum, minimum, extremum | Local properties | `prop` | State the stationary-point theorem and Rolle's theorem. |
| Constantness | Property | `prop` | State the zero-derivative conclusion. |
| Inverse pair and composition | Relations | imported `chap9` props | State inverse and chain rules without rebuilding Chapter 9 vocabulary. |
| L'Hopital assumptions and conclusions | Results with local side conditions | `thm` plus proof-local props | Keep denominator nonvanishing and quotient-limit conclusions visibly connected. |

The epsilon/delta witness predicates `is_difference_quotient_close_to`,
`is_newton_approximation_witness`, local-extremum witnesses, and the
between-points estimate in the L'Hopital proof are useful implementation
relations.  They are not replacements for the public mathematical concepts in
the table.

### Difference quotients and point derivatives

Mathematically, the difference quotient is a function on the punctured domain,
not merely a repeated formula inside an epsilon estimate:

~~~litex
have fn difference_quotient(
    X power_set(R), f fn(z X) R, x0 X
) fn(y set_minus(X, {x0})) R =
    fn(x set_minus(X, {x0})) R {
        (f(x) - f(x0)) / (x - x0)
    }

prop has_derivative_at(
    X power_set(R), f fn(x X) R, x0 X, L R
):
    $chap9::is_limit_point_of_set(X, x0)
    $chap9::has_function_limit(
        set_minus(X, {x0}), difference_quotient(X, f, x0), x0, L
    )

prop is_differentiable_at(X power_set(R), f fn(x X) R, x0 X):
    exist L R st {$has_derivative_at(X, f, x0, L)}

have fn derivative by exist!:
    ? forall X power_set(R), f fn(x X) R, x0 X:
        $is_differentiable_at(X, f, x0)
        =>:
            exist! L R st {$has_derivative_at(X, f, x0, L)}
~~~

`has_derivative_at` is a relation because proofs must compare a supplied
candidate `L`; `derivative` is a canonical selection because later statements
must write its value.  Reject an existence-only API, and reject a proposition
that merely describes a proposed derivative object without making `L`
available as an ordinary real.

The displayed `difference_quotient` is now a checked public construction.  The
kernel instantiates a dependent function return domain when the function is
applied, so `difference_quotient(X, f, x0)(x)` remains defined only for
`x in X - {x0}`.  `has_derivative_at` currently preserves the source's direct
epsilon/delta relation through `is_difference_quotient_close_to`; the checked
bridge theorems connect that relation to the callable quotient and Chapter 9's
function-limit interface.  This keeps existing differential-calculus proofs
stable while making ordinary quotient-limit statements available directly.

`derivative_value_unique` is a theorem with a `uniqueness` edge from
`has_derivative_at`; it must precede the `derivative` selector.  This is the
only necessary local source-order deviation: Tao introduces the notation in
Definition 10.1.1, while Litex must establish unique existence before exposing
the selected function.  The immediate use probe is:

~~~litex
$has_derivative_at(X, f, x0, L)
derivative(X, f, x0) = L
~~~

### Differentiability on a domain and the derivative function

Definition 10.1.11 quantifies only over limit points of `X`.  The ideal
definition must preserve that distinction:

~~~litex
prop is_differentiable_on(X power_set(R), f fn(x X) R):
    forall x X:
        $chap9::is_limit_point_of_set(X, x)
        =>:
            $is_differentiable_at(X, f, x)

prop has_derivative_function_on(
    X power_set(R), f, df fn(x X) R
):
    forall x X:
        $chap9::is_limit_point_of_set(X, x)
        =>:
            $has_derivative_at(X, f, x, df(x))

have fn derivative_function(
    X power_set(R), f fn(z X) R
) fn(y X: $is_differentiable_at(X, f, y)) R =
    fn(x X: $is_differentiable_at(X, f, x)) R {derivative(X, f, x)}
~~~

`has_derivative_function_on` remains necessary even after the canonical
function exists: theorems such as the mean-value and monotonicity theorems
often receive a displayed `df` whose formula is easier to use than repeatedly
unfolding a selector.  By contrast, `derivative_function` is a direct
formula-defined partial function, not a second `exist!` construction.  Its
domain is the differentiability locus, so it does not assign an arbitrary
value at an isolated or nondifferentiable point.

The implemented `is_differentiable_on` follows this limit-point guard.  The
support theorems `non_limit_point_is_isolated` and
`isolated_point_is_continuous_at` supply the other branch of Corollary
10.1.12, without pretending an isolated point has a derivative.  The
representative function-level probe is:

~~~litex
$is_differentiable_at(X, f, x)
$has_derivative_at(X, f, x, derivative_function(X, f)(x))
~~~

### Newton approximation and differential calculus

Newton approximation is a relation between a supplied slope and a supplied
function, not a new tangent-line object:

~~~litex
prop has_newton_approximation_at(
    X power_set(R), f fn(x X) R, x0 X, L R
):
    forall epsilon R+:
        exist delta R+ st {
            forall x X:
                abs(x - x0) <= delta
                =>:
                    abs(f(x) - (f(x0) + L * (x - x0)))
                        <= epsilon * abs(x - x0)
        }
~~~

Proposition 10.1.7 should be a source-facing equivalence theorem between this
relation and `has_derivative_at`.  Directional lemmas may remain as proof
components, but they do not replace the source theorem.  The resulting
dependency shape is:

~~~text
has_derivative_at --proof--> Newton approximation
Newton approximation + limit point --proof--> has_derivative_at
has_derivative_at --proof--> continuity at a point
has_derivative_at --proof--> constant, identity, sum, product,
                              scalar, difference, reciprocal, quotient laws
Newton approximation + composition relation --proof--> chain rule
~~~

The chain rule is a `thm`, not a template.  Its callable composition should
reuse Chapter 9's composition relation or an already well-defined displayed
function `h`; a bare anonymous `fn(x X) R {g(f(x))}` cannot become the
semantic definition when the verifier cannot establish that `f(x)` lies in
`Y`.  The checked Newton-composition proof therefore keeps the displayed
function and exact carrier visible throughout the estimate.

### Extrema, mean values, and monotonicity

`is_local_maximum_at`, `is_local_minimum_at`, and
`is_local_extremum_at` are props.  Their radius-bearing witness forms are
implementation helpers.  The source order and theorem roles are:

~~~text
local extrema + point derivative
  --proof--> local extrema are stationary

Chapter 9 continuity and compact extrema + stationary points
  --proof--> Rolle's theorem
Rolle + an affine auxiliary function
  --proof--> mean value theorem
mean value theorem + restriction to subintervals
  --proof--> bounded derivative is Lipschitz
  --proof--> derivative-sign monotonicity and zero-derivative constancy
~~~

The Chapter 9 monotonicity predicates should remain imported.  In contrast,
`is_constant_on(X,f)` is a useful Chapter 10 property because it is the direct
conclusion of the zero-derivative theorem.  Rolle, the mean-value theorem,
their closed-subinterval transports, and the sign/constant conclusions are
all `thm`s; they do not manufacture new mathematical objects.

Standalone Exercises 10.2.6 and 10.2.7 are outside the maintained textbook
surface, so this chapter pass does not add a Lipschitz interface.  If that
exercise material is requested separately, its quantitative condition should
then be modeled as a real `prop`, not folded into the mean-value theorem.

### Inverses and L'Hopital's rule

An inverse pair is already a Chapter 9 relation.  Chapter 10 consumes
`chap9::is_inverse_pair_on` directly: its inverse is typed
`g fn(y Y) X`, which records its actual codomain instead of merely saying that
a real-valued function happens to land in `X`.  When the Chapter 10 proof
needs the ordinary identity `g(f(x)) = x`, it derives it from Chapter 9's
existential inverse law locally.  The inverse derivative lemma and the
inverse function theorem are theorems depending on that relation, the chain
rule, continuity of the inverse, reciprocal limit laws, and the nonzero
derivative condition.

`inverse_function_difference_quotient_estimate` is a checked proof result, not
a foundational assumption of Analysis I.  It takes the reciprocal of the
forward difference-quotient limit on its nonzero subtype, uses inverse
continuity to map the punctured target domain into that subtype, composes the
two limits, and simplifies the reciprocal quotient pointwise.

For Section 10.5, the nonzero punctured-neighborhood condition is a local
relation used to make the quotient meaningful.  It is not the whole of
Proposition 10.5.1.  The checked source-facing `lhopital_rule_first` returns
both that neighborhood and the quotient-limit conclusion using one radius.
The checked source-facing `lhopital_rule_second` similarly returns both
nonvanishing on `(a,b]` and the right-hand quotient limit.  The second theorem
has this dependency spine:

~~~text
Rolle / Cauchy mean value theorem
  -> pointwise quotient comparison
  -> right-limit transport between the endpoint and the Cauchy point
  -> L'Hopital quotient limit
~~~

The between-points epsilon predicate is a proof helper; it is not a reusable
replacement for `has_function_limit`.

### Typed dependency map and intended build order

The edge labels in this map are `import`, `signature`, `definition`,
`existence`, `uniqueness`, `selection`, `well_definedness`, `proof`, and
`trust/source`.

~~~text
chap9 limit points, function limits, continuity, extrema, monotonicity,
composition, inverse pairs
  --import-->
punctured difference quotient
  --definition--> has_derivative_at
  --definition--> is_differentiable_at
  --proof--> derivative_value_unique
is_differentiable_at + derivative_value_unique
  --existence/uniqueness/selection--> derivative
is_differentiable_at + limit-point guard
  --definition--> is_differentiable_on
has_derivative_at + displayed df
  --definition--> has_derivative_function_on
is_differentiable_at + derivative
  --well_definedness--> derivative_function

has_derivative_at <--> Newton approximation
  --proof--> continuity and differential-calculus laws
  --proof--> chain rule
local extrema + has_derivative_at
  --proof--> stationary points -> Rolle -> mean value theorem
mean value theorem
  --proof--> monotonicity and constantness
chain rule + chap9 inverse pair
  --proof--> inverse derivative and inverse function theorems
Newton approximation / Cauchy mean value / right-limit transport
  --proof--> L'Hopital rules
~~~

Implement in that order.  Keep source-facing definitions and theorems in
their Tao order; only place derivative uniqueness immediately before the
canonical selector, and keep Cauchy mean value as a clearly labeled 10.5
proof-support theorem rather than a fictitious source heading.

### Current boundaries to preserve visibly

- `difference_quotient` now depends on the checked kernel support for
  parameter-dependent function return domains.  Its punctured carrier is part
  of the function type, not an after-the-fact side condition.
- The chain-rule Newton estimate is checked.  Its proof uses the exact
  composition carrier and an explicit transitive epsilon bound.
- The inverse-function estimate and Theorem 10.4.2 are checked; neither adds a
  new primitive concept or trust boundary.
- The domain-level differentiability predicate now follows the source's
  limit-point guard.  Both L'Hopital propositions now have complete
  source-facing theorem interfaces; their proof-support theorems remain
  subordinate to those interfaces.
- No change in this design section licenses a new template, struct,
  `abstract_prop`, compatibility alias, or hidden trust wrapper.
