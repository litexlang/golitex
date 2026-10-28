# Finite probability

This strict source module contains FiniteProbabilitySpace, ten function
families, uniform, Dirac and finite-pushforward bundled constructors, the
independent_events predicate and 104 named theorems. There are
three internal quantified closure facts. No trust, user axioms or abstract
predicates are used. The source reuses bounded native power-set closure; no
reserved theorem names are added.

## Import

```ini
[import std]
prob = probability
```

All names below are in prob::main. The following self-contained mathematical
excerpt is checked in an independent project:

```litex
{2,4,6} $subset {1,2,3,4,5,6}
{2,4,6} $in power_set({1,2,3,4,5,6})
\prob::main::uniform_event_probability<{1,2,3,4,5,6}>({2,4,6}) = 1/2
```

## Interfaces and domains

FiniteProbabilitySpace<Ambient set> stores carrier in power_set(Ambient) and
prob in fn(E power_set(carrier)) R. The carrier is finite and nonempty. The
laws say P({})=0, P(carrier)=1, P(E)>=0 and P(E union F)=P(E)+P(F) for disjoint
events. Nonempty events may have probability zero. The structure accepts supplied spaces; the uniform constructor below
builds an instance with this complete contract.

\conditional_event_probability<Ambient,space>(A,B) has two event arguments
and requires space.prob(B)>0. It returns P(A intersect B)/P(B). The
independent_events(Ambient,space,A,B) predicate means P(A intersect B)=P(A)P(B)
and permits null events without introducing an undefined quotient.

\uniform_event_probability<Omega>(E) requires a finite nonempty Omega and
E in power_set(Omega), returning finite_set_size(E)/finite_set_size(Omega).
Its normalization, nonnegativity and disjoint additivity are proved as source
theorems. uniform_probability_laws(Omega) packages these existing laws, and
\uniform_probability_space<Omega> is the actual bundled value
(Omega,\uniform_event_probability<Omega>) in &FiniteProbabilitySpace<Omega>.
It has the same finite/nonempty guard. In an imported caller, release the
packaging theorem and expose this defining tuple equality before binding a
space alias; the runnable dice example shows each checked step.

\dirac_event_probability<Omega,point>(E) has finite Omega, point in Omega
and E in power_set(Omega), returning finite_set_size(intersect(E,{point})).
It is1 when the point belongs to E and0 otherwise.
\dirac_probability_space<Omega,point> returns the actual tuple
(Omega,\dirac_event_probability<Omega,point>). Its member point proves the
carrier nonempty; there is no instance on an empty carrier. Imported callers
release dirac_probability_laws and expose the tuple, as for the uniform model.

\finite_expectation<Ambient,space>(X) takes an actual function
X: fn(outcome space.carrier) R and returns
finite_set_sum(space.carrier,fn(outcome space.carrier) R
{X(outcome)*space.prob({outcome})}). No positivity of individual atoms is
required. The sampler must be total on the actual carrier and real-valued.
A function on a broader domain needs a checked restriction before passing it.

\finite_variance<Ambient,space>(X) has the same finite real sampler domain
and returns the actual expectation of (X-E(X))^2. It introduces no extra
moment or positivity premise because the sample carrier is finite.

\finite_covariance<Ambient,space>(X,Y) takes two total real functions on
that same carrier and returns E((X-E(X))*(Y-E(Y))). It is symmetric and
Cov(X,X)=Var(X). It has no complex or measure-space overload.

## Named source results

| Family | Names |
| --- | --- |
| Event types | event_operations_are_events, event_probability_types |
| Event arithmetic | event_partition, event_complement, event_difference, event_monotone, event_bounds, event_inclusion_exclusion, event_union_bound, null_event_subsets |
| Conditioning | conditional_event_bounds, conditional_event_product, conditional_event_self, conditional_event_empty, conditional_event_whole, conditional_event_complement, conditional_event_monotone, bayes_event_rule, total_probability_two_events |
| Independence | independent_events_symmetric, independence_implies_conditional, conditional_implies_independence, independence_complement, independence_complement_right, independence_complements, null_event_independent |
| Uniform formula | uniform_event_normalization, uniform_event_nonnegative, uniform_disjoint_additivity, uniform_probability_laws |
| Dirac model | dirac_event_contains, dirac_event_excludes, dirac_probability_laws |
| Further event bounds | event_frechet_bounds, whole_event_independent, conditional_disjoint_events |
| Singleton weights | event_probability_from_singletons |
| Finite pushforward | finite_pushforward_empty, finite_pushforward_whole, finite_pushforward_nonnegative, finite_pushforward_disjoint_additivity, finite_pushforward_probability_laws, finite_pushforward_event_formula, finite_pushforward_singleton_probability |
| Expectation | finite_expectation_formula, finite_expectation_extensional, finite_expectation_nonnegative, finite_expectation_monotone, finite_expectation_vanishes, finite_expectation_zero, finite_expectation_of_constant, finite_expectation_constant, finite_expectation_bounds, finite_expectation_of_linear_combination, finite_expectation_linear, finite_expectation_add, finite_expectation_scale, finite_expectation_subtract, finite_expectation_affine, finite_expectation_square_bound |
| Variance | finite_variance_formula, finite_variance_nonnegative, finite_variance_of_constant, finite_variance_constant, finite_variance_second_moment, finite_variance_of_affine, finite_variance_affine, finite_variance_scale, finite_variance_translate |
| Covariance | finite_covariance_formula, finite_covariance_symmetric, finite_covariance_self, finite_covariance_of_constant_left, finite_covariance_constant_left, finite_covariance_constant_right |
| Covariance moments and bilinearity | finite_covariance_product_moment, finite_covariance_of_linear_combination_left, finite_covariance_linear_combination_left, finite_covariance_of_linear_combination_right, finite_covariance_linear_combination_right, finite_covariance_affine |
| Covariance square and zero cases | finite_covariance_square_bound, finite_covariance_zero_variance_left, finite_covariance_zero_variance_right |
| Variance bounds | finite_variance_parallelogram, finite_variance_add_bound, finite_variance_subtract_bound |
| Variance of combinations | finite_variance_of_linear_combination, finite_variance_linear_combination, finite_variance_add, finite_variance_subtract, finite_variance_add_uncorrelated |

Difference requires B subset A; monotonicity requires A subset B. Bayes
requires both event probabilities positive. Every conditional result keeps
its positive-evidence condition. The independent imported contracts in
examples/probability/finite_events/contracts retain all original domains.

Imported modules do not inject their ordinary universal facts. For generic
compound-event statements, the caller publishes numeric closure facts
using event_probability_types, as shown in those contracts. This adds
no hypotheses to the mathematical results and no global proof strategies.
Template instances use their declared function interfaces directly.

## Verified scope and remaining work

The public caller constructs the six-outcome uniform space and checks
P(even)=1/2, P(>3)=1/2, P(even intersect >3)=1/3 and
P(even | >3)=2/3 using its actual probability function. Independent generic
contracts check the packaging theorem and constructor as well as all prior
laws. Wrong conditional values and conditioning on the empty event are rejected.

The public caller also constructs the point mass at1 on {0,1}: the nonempty
event {0} has probability0, {1} has probability1, and P({0}|{1})=0. The two
events satisfy the same independence definition. Conditioning on {0} is
rejected specifically because its probability is not positive.

The two-event total probability formula is exported with both positive branch
probabilities. The actual dice example checks complementary branch probability
1/2, conditional values2/3 and1/3, and total1/2. Zero first/complement branch
controls reject the corresponding positive premise.

null_event_independent needs P(A)=0 and keeps arbitrary event B, including
null B. Complement preservation needs the original independence relation.
conditional_event_monotone(Omega,space,A,B,E) requires A subset B and P(E)>0.
None of these adds an independence or positivity assumption implicitly.
The finite expectation definition and these elementary laws use the existing
finite-set sums. The actual dice observable k has expectation7/2; the point
mass observable k has expectation1. Replacing its value at the null outcome0
by100 keeps expectation1. Both models also check the constant5 and zero laws.
The singleton-weight formula is proved by induction on finite event cardinality;
constant expectation uses its normalization, not a new assumption.
Measure/countable probability, statistical inference and full probability Lean
compilation remain outside this delivered slice. Finite correlation and image
distributions are described below.

## Checks

```bash
target/release/litex -lang en -strict -f std/probability/main.lit
python3 examples/probability/finite_events/check.py
python3 examples/probability/tail_bounds/check.py --output-dir tmp/2026-10-27/tail-bounds-check
python3 examples/probability/pushforward/check.py --output-dir tmp/2026-10-28/pushforward-check
```

The finite_events checker retains the event/moment contracts and controls
registered in that project. The dedicated tail_bounds checker covers the new
event constructors and inequalities, independent generic/actual/README callers,
its own refusal controls and both installed layouts. Their scopes and historical
receipts are separate. Neither certifies a complete undergraduate probability
course or a repository release.

Known event memberships now directly support union/intersection/difference
arguments in bounded WD checks. Union requires both events in the same
powerset; intersection needs either bound and difference its left bound.
No proof-search ceiling is increased. A separate known-property rule retains
template declaration evidence when widening real call outputs to complex.
It preserves argument/guard WD and every applicable alternative signature.

The two one-bound intersection-finiteness strategies retain the actual finite
operand proof at existing child permissions. A union still needs both sides
finite; an invalid inner expression remains invalid even in an empty
intersection. These are general set rules, without probability-specific cases.

A difference X minus B is an event of X using identity or an actual stored
carrier equality at the existing bounded known-property stage. Existing
stored-left membership evidence keeps priority; wrong carriers and other
function guards remain checked.

Literal-event typing reuses each already recorded point-in-carrier fact at the
bounded known-property stage. It keeps all inner WD, distinctness and independent
call guards. Its generated Lean pair covers the guard, singleton, distinct pair
and carrier alias, with member/order corruption tests. This does not certify
the probability structures themselves in Lean.

Linearity uses real coefficients and two actual real functions on the same
carrier; no independence is needed. The literal-function interface directly
states E(aX+bY)=aE(X)+bE(Y). Addition, scaling, subtraction and affine change
are exported separately. Variance is nonnegative, constants have variance0,
and Var(X)=E(X²)-E(X)² gives E(X)²<=E(X²).

The actual dice example computes E(X²)=91/6 and Var(X)=35/12. The point-mass
observable has Var(X)=0 while taking different values at its two sample points;
there is no erroneous everywhere-constant converse. Negative coefficients,
perfectly dependent inputs and null outcomes remain legal. The refusal
controls check wrong values, missing pointwise relations, total-real sampler
domains, partial functions and arity.

Variance obeys Var(aX+c)=a²Var(X) for all real a,c, including a=0;
scaling and translation have separate interfaces. Dice Var(2X-3)=35/3,
Var(-2X)=35/3 and Var(X+100)=35/12. Dirac affine changes preserve variance0.
A sampler undefined on its carrier is rejected even with coefficient0.
Covariance self-values match35/12 for the dice and0 for the point mass;
symmetry is also checked on the dice observable and its square.

A constant real observable has covariance0 with every total real observable,
on either side. The supplied-function helper requires the actual pointwise
constant relation; direct interfaces construct the constant sampler. Zero,
negative and positive real constants are legal; a nonreal constant is rejected.

## Covariance moments and linear combinations

`finite_covariance_product_moment(Omega,space,X,Y)` proves
Cov(X,Y)=E(XY)-E(X)E(Y). The centered-product definition is unchanged.
All observables are total real functions on the same actual sample carrier.

`finite_covariance_of_linear_combination_left(Omega,space,X,Y,W,H,a,b)`
consumes the pointwise relation H(k)=aX(k)+bY(k) and proves
Cov(H,W)=aCov(X,W)+bCov(Y,W). The right-hand version uses
H(k)=aY(k)+bW(k) and proves Cov(X,H)=aCov(X,Y)+bCov(X,W).
The corresponding names without `of_` construct the literal combination;
they take X,Y,W,a,b after Omega,space. No independence is assumed.

`finite_covariance_affine(Omega,space,X,Y,a,b,c,d)` proves
Cov(aX+b,cY+d)=acCov(X,Y). Coefficients may be zero or negative.
They do not remove the total-real domain of either input.

`finite_variance_of_linear_combination(Omega,space,X,Y,H,a,b)` consumes
H(k)=aX(k)+bY(k) and proves Var(H)=a²Var(X)+2abCov(X,Y)+b²Var(Y).
`finite_variance_linear_combination` constructs that combination, and
`finite_variance_add` / `finite_variance_subtract` specialize its coefficients.
`finite_variance_add_uncorrelated` requires Cov(X,Y)=0 before dropping the
cross term; zero covariance is not a claim of independence.

The actual dice caller uses Y=2X+1, obtaining Cov(X,Y)=35/6,
Var(Y)=35/3, Var(X+Y)=105/4 and Var(X-Y)=35/12. It also exercises
negative and zero coefficients and the Dirac space's null outcome.

The earlier moment/bilinearity checkpoint passed77 CLI checks: four positive projects,71
final-statement refusal controls and both installed layouts at source91/79thms. Generic
contracts82 and actual caller202 statements pass; std/WiX has80 matching files
and unique component references. These focused source and packaging checks do
not imply full probability Lean support or release certification.

## Covariance square and variance bounds

The six covariance-bound interfaces take Omega,space,X,Y, with the same total-real sampler
domains as finite_covariance. finite_covariance_square_bound proves
Cov(X,Y)^2<=Var(X)Var(Y), including either zero variance; no positivity or
independence premise is added. Its proof uses the nonnegative quadratic
Var(tX+Y) and separates its zero leading coefficient before dividing.

finite_covariance_zero_variance_left/right require Var(X)=0 / Var(Y)=0,
respectively, and prove Cov(X,Y)=0. They do not assert everywhere constancy
or independence. finite_variance_parallelogram proves
Var(X+Y)+Var(X-Y)=2Var(X)+2Var(Y); finite_variance_add_bound and
finite_variance_subtract_bound bound each variance by that nonnegative total.

The dedicated examples/probability/covariance_bounds project has independent
generic calls, an actual Bernoulli equality case and a nonconstant Dirac
zero-variance observable. Run its check.py with --output-dir <task-output>
for the focused strict, refusal and installed-layout checks.

The covariance-bounds increment passes14 focused CLI checks: source97/85thms,
six generic interfaces,90 actual example statements, the isolated README, eight
final-statement refusal controls and both installed layouts. std/WiX still has80
matching files/component references. The preceding77 checks describe their
79-thm snapshot; they were not rerun as a claim about all85-thm consumers.

## Finite tail events, Markov and Chebyshev

The ordinary source functions finite_upper_tail_event<Omega,space>(X,a) and
finite_deviation_tail_event<Omega,space>(X,a) have two template parameters and
two ordinary arguments. Both return power_set(space.carrier), for complete
real-valued X on that carrier and any real a. Their exact native set-builder
bodies are respectively {k space.carrier:X(k)>=a} and
{k space.carrier:abs(X(k)-EX)>=a}. Their threshold comparison includes equality.

Four checked source theorems use a in R+:

| Name and ordinary arity | Premises and conclusion |
| --- | --- |
| finite_markov_event_bound/5 | Omega,space,X,A,a; X>=0 on the whole carrier and X>=a on A imply P(A)<=EX/a. |
| finite_chebyshev_event_bound/5 | Omega,space,X,A,a; abs(X-EX)>=a on A implies P(A)<=Var(X)/a^2. |
| finite_markov_tail_bound/4 | Omega,space,X,a; global nonnegative X gives the bound on finite_upper_tail_event. |
| finite_chebyshev_tail_bound/4 | Omega,space,X,a; the same variance bound on finite_deviation_tail_event, with signed X allowed. |

Empty events, nonempty null events and variance0 remain legal. Nonpositive
thresholds are legal for constructing an event, but refuse the inequality
interfaces. Markov's nonnegativity is a pointwise whole-carrier condition; a
nonnegative expectation alone does not replace it. No independence is assumed.

The proof splits the carrier into an event and its complement, compares exact
restricted weighted sums and uses singleton normalization. Chebyshev applies
Markov to the nonnegative centered square. Private checked real/complex scalar
transport introduces no public premise, trust, native rule or strategy.
Named event-valued functions preserve the actual set builders while supplying
a declared codomain for generic theorem headers; direct raw-set probability
comparison headers are not covered by this acceptance.

The dedicated examples/probability/tail_bounds caller checks a fair Bernoulli
upper tail with probability1/2 and centered tail with probability1, both at
attained bounds; a signed sampler; a nonempty Dirac null tail with probability0
and variance0; empty supplied events and an empty native tail. Independent
contracts and threshold/domain/pointwise/strictness refusals accompany it.
At the tail-bound checkpoint, source had103 statements,89 top-level thms,10 templates (eight function
families and two bundled values), one structure, one predicate and two internal
quantified closure facts. Earlier verification counts above remain records of
their exact historical snapshots, not fresh claims about this increment.


This tail increment passes20 focused CLI checks: strict source103/89thms,
six generic contracts,117 actual statements, one isolated README statement,
14 final-statement refusal controls and both installed layouts. The std payload
and WiX have80 matching files and unique component references. The same ongoing
task's pinned1.1.6-beta binary was used; this is not a test claim for concurrent
compiler changes, the whole undergraduate library or a release.


## Finite real correlation

finite_correlation<Omega,space>(X,Y) is an ordinary source function with two
template parameters and two complete real sampler arguments on the actual
carrier. Its definition is Cov(X,Y)/sqrt(Var(X)*Var(Y)). Both variances must
be strictly positive in the function domain. Zero-variance inputs have no
correlation value; this includes nonconstant observables on Dirac spaces.
There is no complex or statistical-estimator overload.

Eight source thms retain those guards: finite_correlation_formula/4,
finite_correlation_symmetric/4, finite_correlation_self/3,
finite_correlation_square_bound/4, finite_correlation_abs_bound/4,
finite_correlation_bounds/4, finite_correlation_zero_from_covariance/4 and
finite_covariance_zero_from_correlation/4. All arity4 calls take
Omega,space,X,Y; self takes Omega,space,X and requires its variance positive.
The two zero directions consume the corresponding covariance0/correlation0
premise. No independence implication is asserted.

The source reuses the covariance square bound and positive real-root arithmetic.
One internal checked scalar root-domain fact supports declaration WD; private
scalar lemmas normalize its square and transport the absolute bound to both
interval bounds. A generic caller that expands the quotient publishes the same
proved scalar root-domain fact, since anonymous module facts are not imported.
Function-valued calls and the other laws retain their declared guard interfaces.
There is no trust, native rule/search/WD, protected AST/state or compiler delta.

At the correlation checkpoint, source had113 top-level statements:97 named thms,11 templates (nine
function families and two bundled values), one structure, one predicate and
three internal closure facts. Dedicated positive/negative/zero correlation
callers and guard controls are in examples/probability/correlation. All20 focused checks pass: source113/97thms, ten generic statements,177 actual
statements, one isolated README,14 final-only refusal controls and both installed
layouts. Four unchanged cold positive outputs were hash-checked and reused after
correcting only three fixture phase labels; all14 controls and two installed
layouts reran. std/WiX80 files/references agree. Earlier receipt counts above
retain their exact snapshots.


## Finite image distributions

finite_pushforward_event_probability<Omega,space,Target,F>(A) has four template
parameters and one event argument. The supplied source is a finite probability
space, F is a complete unary map on its actual carrier into Target, and
A belongs to power_set(fn_range(F)). The real value is
space.prob(preimage_set(F,A)). Target need not be finite and F need not be
injective or onto Target.

finite_pushforward_probability_space<Omega,space,Target,F> is the actual
bundled value (fn_range(F),the event-probability function), of type
&FiniteProbabilitySpace<Target>. Its carrier contains all image points,
including images of zero-mass outcomes. Imported callers release
finite_pushforward_probability_laws and expose its defining tuple before
binding and opening a space alias, as in the other bundled constructors.

Seven source laws prove empty/whole/nonnegative/disjoint-additive probability,
full bundled membership, the inverse-image formula and the singleton-fiber
formula Ppush({y})=P(preimage(F,y)) for y in fn_range(F). The first, second and
bundling laws have ordinary arity4; nonnegative, event formula and singleton
formula have arity5; additivity has arity6. No source law or positive-atom
premise is omitted.

Current source has122 top-level statements:104 named theorems,13 templates
(ten function families and three bundled values), one structure, one predicate
and three internal closure facts. Independent strict source replay and the
100-statement actual caller pass. The dedicated
[pushforward example](../../examples/probability/pushforward/README.md) checks
dice parity masses1/2, a constant map with mass1, and a retained Dirac image
point with mass0. All20 focused checks pass: source122, generic10, actual100, README1,14
final-only refusals and both installed layouts. std/WiX has80 matching payload
files and unique component references. These checks use the ongoing task's
pinned1.1.6-beta executable; earlier receipts retain their historical scopes. Expectation transport,
random-variable independence and countable/measure probability remain open.
