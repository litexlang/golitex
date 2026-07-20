# Mathematical Collections for Tao Analysis I

## Concept-card convention

For each central mathematical concept, record its ordinary meaning, semantic
role, ideal Litex form, representative interface, nearest rejected form,
direct dependencies, one downstream use, and any honest proof or language
boundary.  These are separate questions: a concept can be a function while
its current unique-existence proof is trusted, or a property while every
theorem about it is checked.  Knowledge state never changes the mathematical
role of the concept.

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
    forall epsilon R_pos:
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
            $has_limit(fn(i N_pos) R {a(i) + b(i)}, x + y)
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
    ? forall x R_pos, q Q:
        $has_limit(rational_power_approx_seq(x, fn(n N_pos) R {q}), x^q)
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
mode.  The default project export currently uses the trusted/affect-only path,
so the generated Chapter 6 artifact marks these declarations as direct
`trust`, records their project-export trust source, and does not pretend that
skipped proof bodies produced proof edges.  A strict project run currently
stops at the existing Chapter 5 trust boundary before it reaches Chapter 6.
The proof edges above therefore remain part of this human contract until that
upstream debt is cleared and a strict run can emit them.

## Chapter 11: Riemann integration

This is the design map for the important Chapter 11 interfaces. It specifies
the intended mathematical surface, not a claim that every supporting theorem is
already checked. A later proof should read like ordinary analysis:

~~~litex
$is_riemann_integrable_on(I, f)
integral_on(I, f)
$has_riemann_integral(I, f, s)
~~~

The first is a condition, the second is the selected value, and the third
relates an externally supplied value to that selection. Do not replace a value
or construction with a prop merely because its existence proof is unfinished.

## Form-selection policy

- Use prop for conditions and relations: bounded interval, partition,
  refinement, piecewise constancy, majorization, and integrability.
- Use have fn for named maps, set-valued constructions, finite constructions,
  and selected numerical values that later mathematics applies.
- Use have fn ... by exist! for canonical values whose existence and uniqueness
  are genuine obligations: interval length, common refinement, Riemann sums,
  upper/lower integrals, and the final integral. When an API would otherwise
  quantify over a subtype such as finite_set, move that subtype fact into the
  function domain and keep the parameter carrier an ordinary object set.
- Use thm for reusable propositions, criteria, and algebraic laws. A theorem
  proves a fact; it is not a substitute for a function that callers apply.
- Use template only for a genuinely parameter-indexed local declaration family.
  The central interfaces below take ordinary parameters and should be direct
  props or functions, not templates.
- Do not use abstract_prop for Chapter 11 vocabulary. These are internally
  defined mathematical notions. A proof gap can be explicit debt, but it does
  not change whether a concept is a function, object, or relation.

## Interval geometry

### Bounded intervals and connectedness

A bounded interval is one of the four endpoint forms with real endpoints.
Degenerate endpoint forms already cover singleton and empty intervals; they do
not need new wrapper types. Connectedness is a property used to characterize
these domains, not the carrier for integration.

~~~litex
prop has_interval_endpoints(I power_set(R), a, b R):
    I = '[a, b] or I = '[a, b) or I = '(a, b] or I = '(a, b)

prop is_bounded_interval(I power_set(R)):
    exist a, b R st {$has_interval_endpoints(I, a, b)}

prop is_connected_subset_of_R(X power_set(R)):
    forall x, y, z R:
        x $in X
        y $in X
        x <= z
        z <= y
        =>:
            z $in X
~~~

These are props because later theorems assert them. Reject a separate
bounded-interval object or an abstract predicate: power_set(R) is the carrier
and the endpoint constructors are builtin. Endpoint membership and interval
intersection theorems feed bounded-connected characterization, length,
partitions, and every later integral domain.

### Interval length

Length is a value used inside finite sums, so it is a function, not only a
relation.

~~~litex
prop has_interval_length(I power_set(R), l R):
    exist a, b R st {
        $has_interval_endpoints(I, a, b),
        l = finite_set_max(union({b - a}, {0}))
    }

have fn interval_length by exist!:
    ? forall I power_set(R):
        $is_bounded_interval(I)
        =>:
            exist! l R st {$has_interval_length(I, l)}
~~~

The relation is the specification needed for existence and uniqueness. The
selected interval_length(I) is the ordinary value used by downstream formulas.
Reject an is_length_of_interval prop as the only API: every sum would then
carry an unnecessary witness. The endpoint-representation uniqueness proof is
debt behind this function, not a reason to change its form.

## Finite decompositions

### Partitions and refinement

A partition is a finite family with unique coverage. Refinement is a relation
between two such families.

~~~litex
prop is_partition_of_bounded_interval(I power_set(R), P finite_set):
    $is_bounded_interval(I)
    forall J P:
        J $in power_set(R)
        $is_bounded_interval(J)
        J $subset I
    forall x I:
        exist! J P st {J $in power_set(R), x $in J}

prop is_finer_partition_than(I power_set(R), P2, P1 finite_set):
    $is_partition_of_bounded_interval(I, P2)
    $is_partition_of_bounded_interval(I, P1)
    forall J P2:
        exist K P1 st {J $subset K}
~~~

Both are props: mathematics checks whether a displayed finite family has the
property. They depend on interval geometry and feed finite additivity,
piecewise-constant functions, Riemann sums, and all later gluing arguments.

### Common refinement

The common refinement P#Q is an actual finite set, not merely an existential
fact. Keep the relational specification, but expose the selected construction.

~~~litex
prop is_common_refinement_of_partitions(I power_set(R), P, Q, Rf finite_set):
    $is_partition_of_bounded_interval(I, P)
    $is_partition_of_bounded_interval(I, Q)
    $is_partition_of_bounded_interval(I, Rf)
    forall H Rf:
        exist J P, K Q st {H = intersect(J, K)}
    forall J P, K Q:
        exist H Rf st {H = intersect(J, K)}

have fn common_refinement by exist!:
    ? forall I power_set(R), P, Q power_set(power_set(R)):
        $is_finite_set(P)
        $is_finite_set(Q)
        $is_partition_of_bounded_interval(I, P)
        $is_partition_of_bounded_interval(I, Q)
        =>:
            exist! Rf power_set(power_set(R)) st {
                $is_finite_set(Rf),
                $is_common_refinement_of_partitions(I, P, Q, Rf)
            }
~~~

This function is needed as an input to finite sums and comparison proofs.
The object carrier is a family of real subsets; finite_set remains a fact in
the domain because the current function-selector rule accepts object carriers,
not subtype parameters. A small bridge theorem derives
`P $in power_set(power_set(R))` from a partition. Reject a template for P#Q:
P and Q are ordinary arguments, not parameters creating a new declaration
family.

### Refinement fibers and finite regrouping

After a fine partition has been related to a coarse partition, the next real
object is not a new integral: it is the family of nonempty fine pieces sitting
inside one coarse piece.  This is the unit on which a finite sum is regrouped.
Empty pieces are excluded: they are contained in every coarse piece and hence
cannot be assigned uniquely, while their length and rectangle contributions
are zero.

~~~litex
prop is_refinement_fiber(Pfine power_set(power_set(R)), K power_set(R), F power_set(power_set(R))):
    $is_finite_set(Pfine)
    $is_finite_set(F)
    F $subset Pfine
    forall J F:
        $is_nonempty_set(J)
        J $subset K
    forall J Pfine:
        $is_nonempty_set(J)
        J $subset K
        =>:
            J $in F

have fn refinement_fiber by exist!:
    ? forall Pfine power_set(power_set(R)), K power_set(R):
        $is_finite_set(Pfine)
        =>:
            exist! F power_set(power_set(R)) st {
                $is_refinement_fiber(Pfine, K, F)
            }

have fn refinement_owner by exist!:
    ? forall I power_set(R), Pfine, Pcoarse power_set(power_set(R)), J power_set(R):
        $is_finite_set(Pfine)
        $is_finite_set(Pcoarse)
        $is_finer_partition_than(I, Pfine, Pcoarse)
        J $in Pfine
        $is_nonempty_set(J)
        =>:
            exist! K power_set(R) st {K $in Pcoarse, J $subset K}

thm refinement_fiber_partitions_coarse_piece:
    ? forall I power_set(R), Pfine, Pcoarse, F finite_set, K power_set(R):
        $is_finer_partition_than(I, Pfine, Pcoarse)
        K $in Pcoarse
        $is_refinement_fiber(Pfine, K, F)
        =>:
            $is_partition_of_bounded_interval(K, F)

prop has_refinement_fiber_sum(
    Pfine power_set(power_set(R)), K power_set(R), h fn(J Pfine) R, s R
):
    $is_finite_set(Pfine)
    exist F finite_set st {$is_refinement_fiber(Pfine, K, F), s = finite_set_sum(F, fn(J F) R {h(J)})}

have fn refinement_fiber_sum by exist!:
    ? forall Pfine power_set(power_set(R)), K power_set(R), h fn(J Pfine) R:
        $is_finite_set(Pfine)
        =>:
            exist! s R st {$has_refinement_fiber_sum(Pfine, K, h, s)}
~~~

`is_refinement_fiber` is a prop: callers need to say that a displayed family
is exactly the pieces below `K`.  `refinement_fiber` is a selected object, not
a prop or a template; its specification, uniqueness, and imported use are
carried by `refinement_fiber_has_value`.  The current selector has the raw
family carrier `power_set(power_set(R))`, so the theorem deliberately accepts
an explicit `F finite_set` together with that specification.  The ideal range
type is `finite_set`; carrying finiteness through this raw-selector boundary
is a current Litex interface limitation, not a reason to hide the fiber behind
an existential-only predicate.  The checked
`refinement_fiber_has_finite_representative` theorem gives callers precisely
that finite representative.  `refinement_fiber_sum` is a real selected value:
it is the inner finite sum for a supplied weight `h`, and its relation and
`refinement_fiber_sum_has_value` theorem make it usable across imports.

`refinement_owner` is the complementary selected object. Given a nonempty
fine piece, it returns its unique containing coarse piece. Its raw-family
parameters and explicit finiteness facts are deliberate: the current
`have fn ... by exist!` mechanism accepts object carriers rather than a
`finite_set` parameter. The owner theorem is where a nonempty-set fact is
opened to a local existential member; this is a narrow builtin existential
rule, not a global choice function. Empty pieces remain outside the owner
domain, exactly because no unique owner exists for them.

The two selected views are now linked in both directions.  The checked theorem
`refinement_owner_is_in_refinement_fiber` puts each nonempty fine piece in the
fiber of its owner.  Conversely,
`refinement_fiber_member_has_owner` says that a member of the fiber below a
displayed coarse piece has that coarse piece as its owner.  These are the
ordinary mathematical membership/ownership facts; they are not a substitute
for the remaining equality of two finite sums.

`nonempty_refinement_support(Pfine)` is the finite family of nonempty fine
pieces. It is the correct source carrier for regrouping: an empty fine piece
has no owner, while the source summands used later vanish on it. The checked
theorem `refinement_fiber_family_is_finite_unique_cover` says that any displayed
family equal pointwise to `refinement_fiber(Pfine, K)` is a finite unique cover
of that support, indexed by the coarse partition. Thus Chapter 11 hands the
generic finite-sum theorem exactly a cover, rather than encoding the
refinement mechanism into its numerical statement.

The checked dependency route is:

~~~text
is_finer_partition_than + K in Pcoarse
  + is_refinement_fiber(Pfine, K, F)
  -> is_partition_of_bounded_interval(K, F)

is_finer_partition_than + J in Pfine + is_nonempty_set(J)
  -> refinement_owner(I, Pfine, Pcoarse, J) in Pcoarse
  -> J subset refinement_owner(I, Pfine, Pcoarse, J)
  -> J in refinement_fiber(Pfine, refinement_owner(I, Pfine, Pcoarse, J))

is_finer_partition_than + K in Pcoarse
  + J in refinement_fiber(Pfine, K)
  -> refinement_owner(I, Pfine, Pcoarse, J) = K

refinement_fiber_family(Pfine, Pcoarse)
  -> is_finite_unique_cover_of(nonempty_refinement_support(Pfine), Pcoarse, ...)
~~~

The next theorem is a theorem, not a selected numerical object.  For a weight
`h` on the fine pieces whose empty-piece value is zero, its ideal conclusion is
the finite reindexing identity

~~~text
sum_{J in Pfine} h(J)
  = sum_{K in Pcoarse} sum_{J in refinement_fiber(Pfine, K)} h(J).
~~~

Its intended Litex statement is the following; it is deliberately recorded as
the next theorem, not as an implemented claim yet.

~~~litex
thm finite_set_sum_regroups_over_refinement:
    ? forall I power_set(R), Pfine, Pcoarse finite_set, h fn(J Pfine) R:
        Pfine $in power_set(power_set(R))
        Pcoarse $in power_set(power_set(R))
        $is_finer_partition_than(I, Pfine, Pcoarse)
        forall J Pfine:
            not $is_nonempty_set(J)
            =>:
                h(J) = 0
        =>:
            finite_set_sum(Pfine, h)
            = finite_set_sum(Pcoarse, fn(K Pcoarse) R {refinement_fiber_sum(Pfine, K, h)})
~~~

It depends on the fiber-partition theorem and finite-sum reindexing.  It will
then be instantiated with interval lengths and rectangle contributions, both
of which vanish on empty pieces.  Do not add a trusted `regrouped_sum`
function: regrouping asserts an equality for a class of weights, so its correct
semantic role is `thm`.

### Generic finite indexed families

The preceding theorem is one instance of a reusable finite-combinatorics
interface, not an Analysis-specific construction. A displayed family is a
function from a finite index family to finite subfamilies of one source family;
the family condition, its inner-sum relation, and unique cover are props, while
reindexing is a thm.

~~~litex
prop is_finite_indexed_subfamily(
    U set, S, T finite_set, F fn(K T) power_set(U)
):
    S $subset U
    forall K T:
        $is_finite_set(F(K))
        F(K) $subset S

prop has_indexed_fiber_sum(
    U set, S, T finite_set, F fn(K T) power_set(U), h fn(x U) R, K T, s R
):
    $is_finite_indexed_subfamily(U, S, T, F)
    exist A finite_set st {
        A = F(K)
        A $subset S
        A $subset U
        s = finite_set_sum(A, fn(x A) R {h(x)})
    }

prop is_finite_unique_cover_of(
    U set, S, T finite_set, F fn(K T) power_set(U)
):
    $is_finite_indexed_subfamily(U, S, T, F)
    forall x S:
        exist! K T st {x $in F(K)}

thm finite_set_sum_over_unique_cover:
    ? forall U set, S, T finite_set, F fn(K T) power_set(U), h fn(x U) R, g fn(K T) R:
        $is_finite_unique_cover_of(U, S, T, F)
        forall K T:
            $has_indexed_fiber_sum(U, S, T, F, h, K, g(K))
        =>:
            finite_set_sum(S, fn(x S) R {h(x)}) = finite_set_sum(T, g)
~~~

This is the ideal dependent-family notation. `is_finite_unique_cover_of` is a
prop because it is a condition that a caller proves about a displayed family;
it must not be encoded by selecting an owner function, although a local owner
selector can be derived from its unique-existence clause when a later proof
needs one. `has_indexed_fiber_sum` is deliberately relational: the displayed
outer function `g` carries the inner sums, and the theorem checks its pointwise
meaning. The weight is defined on the common ambient carrier `U`, so the
theorem restricts it only where it is summed; deleting an index never asks the
caller to invent a new function. The finite-sum reindexing conclusion is a
thm, not an object or template.

Chapter 11 now implements this relation-first core on its actual carrier of
families of real subsets: `$is_finite_indexed_subfamily`,
`$has_indexed_fiber_sum`, and `$is_finite_unique_cover_of`, together with the
checked existence and uniqueness theorems for an individual indexed fiber
sum. Its checked base theorem
`finite_set_sum_over_singleton_unique_cover` proves the one-index case: a
unique cover of `S` indexed by `{K}` has `S = F(K)`, so its total sum is the
verified fiber sum at `K`. This is the base case of the intended finite-index
induction, not a special Riemann fact. The checked structural theorem
`finite_unique_cover_distinct_fibers_are_disjoint` derives pairwise fiber
disjointness from the same cover condition, which is exactly the premise of
finite-set disjoint-union addition. The checked
`finite_unique_cover_residual_after_removing_index` and
`indexed_fiber_sum_persists_after_removing_index` show that deleting one index
leaves a unique cover of the complementary family and preserves every
remaining displayed inner sum. The carrier-polymorphic version displayed above
remains ideal design:
`have fn ... by exist!` currently only accepts object parameters, so it cannot
provide one uniform selected sum for arbitrary `finite_set` carriers and a
higher-order family parameter while retaining an importable value theorem.

The remaining general `finite_set_sum_over_unique_cover` induction step is a
generic finite-combinatorics theorem. Existing Fubini handles only uniform
Cartesian products; it does not prove this disjoint indexed-cover law. Its
checked structural preparation now removes one index, restricts the remaining
family to the complement of that fiber, and preserves every remaining inner
sum under the same ambient weight. What remains is to state the finite-set
induction over index families and join its hypothesis to the two disjoint-union
sum identities. It belongs in a reusable finite-sum interface, not in a
Chapter-11-specific matcher. A template remains a rejected escape hatch: it
would hide the relationship between a fiber value and the original summand
instead of giving the theorem the explicit `g` relation.

## Step functions

### Constantness and piecewise constancy

~~~litex
prop has_constant_value_on_subset(
    I power_set(R), E power_set(R), f fn(x I) R, c R
):
    E $subset I
    forall x E:
        f(x) = c

prop is_piecewise_constant_with_partition(
    I power_set(R), P finite_set, f fn(x I) R
):
    $is_partition_of_bounded_interval(I, P)
    forall J P:
        $is_constant_on_subset(I, J, f)

prop is_piecewise_constant_on(I power_set(R), f fn(x I) R):
    exist P finite_set st {$is_piecewise_constant_with_partition(I, P, f)}
~~~

These are props because later proofs assert them and obtain witnesses. A
constant value on an empty piece is not canonical, so it remains a relation
rather than a globally selected function.

### Step-integral values

A weighted contribution is canonical even on an empty piece, because its
length is zero. It should therefore be a selected value; the contribution
family used to justify a finite sum is implementation scaffolding rather than
a primary public API.

~~~litex
have fn piecewise_constant_integral_piece_contribution by exist!:
    ? forall I, J power_set(R), f fn(x I) R:
        $is_bounded_interval(J)
        $is_constant_on_subset(I, J, f)
        =>:
            exist! t R st {
                $has_piecewise_constant_integral_piece_contribution(I, J, f, t)
            }

have fn piecewise_constant_integral_with_partition(
    I power_set(R), P power_set(power_set(R)), f fn(x I) R:
    $is_finite_set(P),
    $is_piecewise_constant_with_partition(I, P, f)
) R =
    finite_set_sum(P, fn(J P) R {
        piecewise_constant_integral_piece_contribution(I, J, f)
    })

have fn piecewise_constant_integral by exist!:
    ? forall I power_set(R), f fn(x I) R:
        $is_piecewise_constant_on(I, f)
        =>:
            exist! s R st {$has_piecewise_constant_integral(I, f, s)}
~~~

The last function becomes valid after partition independence. Its key
dependencies are interval length, partitions, common refinement, and finite
regrouping. It is the concrete base for Darboux values and the identity-alpha
Stieltjes bridge.

## Darboux, Riemann sums, and the Riemann integral

### Order envelopes

Majorization and minorization are pointwise relations. Candidate-value
collections are set-valued functions, and their extrema are selected objects.

~~~litex
prop majorizes_on(I power_set(R), g, f fn(x I) R):
    forall x I:
        f(x) <= g(x)

prop minorizes_on(I power_set(R), g, f fn(x I) R):
    forall x I:
        g(x) <= f(x)

have fn upper_riemann_integral_candidate_values(
    I power_set(R), f fn(x I) R
) power_set(R) = {s R: $is_upper_riemann_integral_candidate_value(I, f, s)}

have fn upper_riemann_integral by exist!:
    ? forall I power_set(R), f fn(x I) R:
        $is_bounded_interval(I)
        $chap9::is_bounded_function_on(I, f)
        =>:
            exist! U R st {$has_upper_riemann_integral(I, f, U)}
~~~

The lower integral has the symmetric shape. The candidate predicate and
has_upper_riemann_integral relation specify the functions; they are not a
second public definition of integration.

### Riemann sums

An upper or lower Riemann sum is a number attached to one function and one
partition. It must be callable, not only asserted to exist.

The checked Chapter 11 API first selects each empty/nonempty piece value, then
uses `$fn_eq` to turn pointwise contribution uniqueness into equality of
contribution families before applying `finite_set_sum`. This explicit middle
step avoids asking the verifier to rediscover a finite induction from an
unfolded universal fact.

~~~litex
have fn upper_riemann_sum_piece by exist!:
    ? forall I, J power_set(R), f fn(x I) R:
        $is_bounded_interval(J)
        J $subset I
        $chap9::is_bounded_function_on(I, f)
        =>:
            exist! t R st {$has_upper_riemann_sum_piece_contribution(I, J, f, t)}

have fn upper_riemann_sum by exist!:
    ? forall I power_set(R), P power_set(power_set(R)), f fn(x I) R:
        $is_finite_set(P)
        $is_partition_of_bounded_interval(I, P)
        $chap9::is_bounded_function_on(I, f)
        =>:
            exist! U R st {$has_upper_riemann_sum(I, P, f, U)}

thm upper_riemann_sum_has_value:
    ? forall I power_set(R), P power_set(power_set(R)), f fn(x I) R:
        $is_finite_set(P)
        $is_partition_of_bounded_interval(I, P)
        $chap9::is_bounded_function_on(I, f)
        =>:
            $has_upper_riemann_sum(I, P, f, upper_riemann_sum(I, P, f))
~~~

Lower sums mirror these declarations, including
`lower_riemann_sum_piece_has_value` and `lower_riemann_sum_has_value`. The
existing contribution-family props remain verifier bridges; they should not be
the first names a mathematical caller has to manipulate. The Darboux/Riemann
comparison is a thm linking these selected sums to the upper/lower envelope
values.

### Integrability and the selected integral

~~~litex
prop is_riemann_integrable_on(I power_set(R), f fn(x I) R):
    $is_bounded_interval(I)
    $chap9::is_bounded_function_on(I, f)
    upper_riemann_integral(I, f) = lower_riemann_integral(I, f)

prop has_riemann_integral(I power_set(R), f fn(x I) R, s R):
    $is_riemann_integrable_on(I, f)
    s = upper_riemann_integral(I, f)

have fn integral_on by exist!:
    ? forall I power_set(R), f fn(x I) R:
        $is_riemann_integrable_on(I, f)
        =>:
            exist! s R st {$has_riemann_integral(I, f, s)}
~~~

Use integral_on(I,f) in algebraic laws and source statements. Keep
has_riemann_integral for theorems that supply a value. Reject a value relation
as the sole API because it obscures canonical substitution.

Small oscillation, closed trims, piecewise continuity, and piecewise
monotonicity are props. Their criteria are thms concluding
is_riemann_integrable_on; they should not select a preferred partition because
ordinary proofs need existence for each epsilon and can use different
partitions.

## Riemann--Stieltjes integration

Alpha-length is a value, while monotonicity of alpha and Stieltjes
integrability are properties. The Stieltjes layer should mirror the ordinary
Riemann layer rather than introduce templates solely to duplicate it.

~~~litex
prop has_alpha_interval_length(alpha fn(x R) R, I power_set(R), l R):
    $is_bounded_interval(I)
    forall a, b R:
        $has_interval_endpoints(I, a, b)
        a < b
        =>:
            l = alpha(b) - alpha(a)
    forall a, b R:
        $has_interval_endpoints(I, a, b)
        b <= a
        =>:
            l = 0

have fn alpha_interval_length by exist!:
    ? forall alpha fn(x R) R, I power_set(R):
        $is_bounded_interval(I)
        =>:
            exist! l R st {$has_alpha_interval_length(alpha, I, l)}

prop has_piecewise_constant_stieltjes_integral(
    I power_set(R), alpha fn(x R) R, f fn(x I) R, s R
):
    $is_piecewise_constant_on(I, f)
    exist P finite_set st {
        $is_piecewise_constant_with_partition(I, P, f),
        $has_piecewise_constant_stieltjes_integral_with_partition(I, P, alpha, f, s)
    }

have fn piecewise_constant_stieltjes_integral by exist!:
    ? forall I power_set(R), alpha fn(x R) R, f fn(x I) R:
        $is_piecewise_constant_on(I, f)
        $chap9::is_monotone_increasing_on(R, alpha)
        =>:
            exist! s R st {$has_piecewise_constant_stieltjes_integral(I, alpha, f, s)}

prop is_riemann_stieltjes_integrable_on(
    I power_set(R), alpha fn(x R) R, f fn(x I) R
):
    $is_bounded_interval(I)
    $chap9::is_monotone_increasing_on(R, alpha)
    upper_riemann_stieltjes_integral(I, alpha, f) =
        lower_riemann_stieltjes_integral(I, alpha, f)

have fn stieltjes_integral_on by exist!:
    ? forall I power_set(R), alpha fn(x R) R, f fn(x I) R:
        $is_riemann_stieltjes_integrable_on(I, alpha, f)
        =>:
            exist! s R st {$has_riemann_stieltjes_integral(I, alpha, f, s)}
~~~

The desired alpha-length selector is the `have fn ... by exist!` shown above.
The current source-facing function is still a narrow trusted selector, because
its all-endpoint uniqueness proof is not yet formalized, but it now has the
real relation `$has_alpha_interval_length` and the checked bridge theorem
`alpha_interval_length_has_value`. Thus callers can state and transport the
mathematical specification without treating the trusted declaration itself as
the only interface.

`has_piecewise_constant_stieltjes_integral` and its selected value are the
Stieltjes analogues of the ordinary step-integral relation and value.  The
value is not a second name for `stieltjes_integral_on`: it is the finite,
piecewise-constant base case used to define the candidate envelopes.  Its
partition-independence theorem depends on exactly the generic finite-family
reindexing bridge above, with `alpha_interval_length` in place of ordinary
length.  In the current Chapter 11 implementation this base remains an
explicit relation named
`has_piecewise_constant_riemann_stieltjes_integral`; do not add the selector
until its uniqueness is supplied by that real partition-independence theorem.
The final envelope selectors `upper_riemann_stieltjes_integral`,
`lower_riemann_stieltjes_integral`, and `stieltjes_integral_on` are already
implemented.

The identity-integrator theorem is a thm equating `stieltjes_integral_on` with
`integral_on`. This layer depends on partitions, finite regrouping, step
integrals, and the ordinary order-envelope architecture.

## Fundamental theorems and change of variables

The integral from the left endpoint is a function of x, not a prop. Its
specification needs a restriction of f to the changing interval [a,x].

~~~litex
prop is_restriction_to_subset(I, J power_set(R), f fn(x I) R, g fn(x J) R):
    J $subset I
    forall x J:
        g(x) = f(x)

prop has_integral_from_left_endpoint(
    a, b R, f fn(t '[a, b]) R, x '[a, b], s R
):
    a < b
    exist g fn(u '[a, x]) R st {
        $is_restriction_to_subset('[a, b], '[a, x], f, g),
        $has_riemann_integral('[a, x], g, s)
    }

have fn integral_from_left_endpoint(
    a, b R, f fn(t '[a, b]) R, x '[a, b]
) R by exist!:
    ? forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
        a < b
        =>:
            exist! s R st {
                exist g fn(u '[a, x]) R st {
                    $is_restriction_to_subset('[a, b], '[a, x], f, g),
                    $has_riemann_integral('[a, x], g, s)
                }
            }

thm integral_from_left_endpoint_has_value:
    ? forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
        a < b
        =>:
            $has_integral_from_left_endpoint(
                a, b, f, x, integral_from_left_endpoint(a, b, f, x)
            )

prop is_integral_function_from_left_endpoint(
    a, b R, f fn(t '[a, b]) R, F fn(x '[a, b]) R
):
    forall x '[a, b]:
        $has_integral_from_left_endpoint(a, b, f, x, F(x))

prop is_antiderivative_of(I power_set(R), f fn(x I) R, F fn(x I) R):
    forall x I:
        $chap10::has_derivative_at(I, F, x, f(x))

prop maps_closed_interval_to_closed_interval(
    a, b, u, v R, phi fn(x R) R
):
    a <= b
    u <= v
    forall x '[a, b]:
        phi(x) $in '[u, v]

prop is_composition_on_closed_interval(
    a, b, u, v R, phi fn(x R) R,
    f fn(y '[u, v]) R, h fn(x '[a, b]) R
):
    $maps_closed_interval_to_closed_interval(a, b, u, v, phi)
    forall x '[a, b]:
        h(x) = f(phi(x))
~~~

The desired function shape is known, but Litex currently rejects the changing
result domain fn(u '[a,x]) R. This is a kernel_problem about dependent
restriction-valued functions, not a reason to weaken the construction into an
existence-only predicate. Keep the trusted selector narrow until the language
supports that construction. The FTCs, antiderivatives-differ-by-a-constant,
integration by parts, and change of variables are thms consuming `integral_on`
or `stieltjes_integral_on`. `is_antiderivative_of`,
`maps_closed_interval_to_closed_interval`, and
`is_composition_on_closed_interval` are props because they describe hypotheses
about displayed functions; no new selected ``substitution map'' should be
invented. The current chapter already follows this classification.

The Chapter 11 selector remains narrowly trusted because of the dependent
restriction-valued function, but `$has_integral_from_left_endpoint` and
`integral_from_left_endpoint_has_value` now expose its ordinary mathematical
specification to callers. That relation is the right bridge for FTC proofs;
the global predicate `is_integral_function_from_left_endpoint` describes a
displayed function that has those values for every x. The checked theorem
`selected_left_endpoint_integral_is_integral_function` supplies the canonical
selector as one such displayed function; it is not a replacement definition
for the relational predicate.

## Dependency order

~~~text
endpoint forms and membership
  -> bounded intervals and connectedness
  -> interval_length
  -> partitions -> refinement -> common_refinement
  -> finite partition additivity and regrouping

constant-on-piece -> piecewise-constant-with-partition
  -> selected piece contribution
  -> step integral with a partition
  -> partition independence -> piecewise_constant_integral

piecewise constant + majorizes/minorizes
  -> upper/lower candidate-value sets
  -> upper/lower Riemann integrals
  -> Riemann integrability -> integral_on

partition + function-value extrema
  -> upper/lower Riemann sums
  -> Darboux/Riemann comparison
  -> continuity and monotonicity criteria
  -> is_riemann_integrable_on

alpha_interval_length + the same partition/step machinery
  -> piecewise-constant Stieltjes integral
  -> upper/lower Stieltjes values
  -> Stieltjes integrability -> stieltjes_integral_on
  -> identity-alpha bridge to integral_on

integral_on + restriction to [a,x]
  -> integral_from_left_endpoint
  -> first FTC -> antiderivative theorems
  -> integration by parts and change of variables
~~~

Implementation should follow this order. Do not add new trusted wrapper APIs to
prove the large algebraic laws, FTC, or change of variables before finite
partition additivity, common-refinement regrouping, and Darboux/Riemann
comparison have their real interfaces.

## Explicit proof and language boundaries

- Finite partition additivity and regrouping are the shared mathematical bridge
  for Section 11.1, step-integral independence, Darboux comparison,
  continuity/piecewise criteria, and Stieltjes gluing. Develop them once at the
  partition layer.
- The required finite-family reindexing is generic: a finite indexed cover is
  a prop, and its sum-reindexing law is a thm.  Do not implement it as a
  Chapter-11-specific matcher; first make a supercarrier function restrictable
  to a variable verified subset.
- Imported set-valued functions need a usable membership or unfolding theorem
  when their defining equation cannot be unfolded across a module boundary.
  This is an interface or kernel issue, not a reason for a duplicate wrapper.
- The changing-domain restriction in the first FTC is a dependent-codomain
  kernel blocker. Keep the intended have-fn shape visible and keep trust
  exactly on that construction.
- The current proof blockers remain in
  scripts/Analysis/todo/03_integration_and_language_blockers.md. This document
  fixes the intended mathematics so later proof work does not redesign the
  public surface while closing them.
