# Mathematical Collections: Probability Theory

## Purpose and scope

This standalone module models the elementary measure-theoretic foundation of
probability through the Kolmogorov axioms. The source of truth is the standard
mathematical identity of a probability space `(Omega, events, probability)`:
`events` is a sigma-algebra on `Omega`, and `probability` is a nonnegative,
normalized, countably additive real-valued set function. The current module
includes generated sigma algebras, the Borel sigma algebra on `R`, the derived
event-probability calculus, countable event limits, continuity of probability,
null and almost-sure events, the first Borel--Cantelli lemma, conditional
probability, independence, measurable maps, real-valued random variables, and
Dirac, conditioned, finite atomic, and pushforward probability constructions.
It excludes Caratheodory extension from premeasures or outer measures,
Lebesgue measure, integration, expectation, almost-sure convergence, laws of
large numbers, and central limit theorems.

The intended readers are users who want to see the probability-theory layer
that conceptually precedes the finite calculations in
`8_probability_and_statistics_in_nutshell`.

## Modeling conventions

`Omega` and value spaces are ordinary Litex carriers. A sigma-algebra is a
supplied value in `power_set(power_set(Omega))`; an event is therefore an
ordinary subset that belongs to that family. Countable families use positive
natural indices, matching Litex's existing sequence interface. A real series
sum remains a relation defined by convergence of partial sums, rather than an
unjustified selected `infinite_sum` function.

Settings carry theorem-wide ambient data and laws. Separate value-level
interfaces now construct generated sigma algebras and push source probability
through measurable maps. The sigma-algebra setting exposes the
whole-space and binary-intersection laws, and the probability setting exposes
the empty-event zero law, even though all three are derivable from smaller
axiom bases; these are conservative, standard projection laws that make the
public interface usable without changing its models.

## Mathematical spine

### Countable union

- **Ordinary meaning:** The subset containing exactly the points that occur in
  at least one set of a positive-natural-indexed family.
- **Semantic role:** Set-valued construction.
- **Ideal Litex form:** The first-class builtin
  `index_union(N+, Omega, family)` with an exact
  `family fn(n N+) power_set(Omega)` signature.
- **Interface sketch:**
  `index_union(N+, Omega, fn(n N+) power_set(Omega) {events_family(n)})`.
- **Nearest wrong alternative:** A chapter-local membership `prop` plus a
  templated set-builder duplicates the general indexed-family construction
  and forces proofs to fold that private representation.
- **Dependencies:** Native sets, exact-domain functions, existential indexed
  fiber witnesses, and the indexed-union builtin (`signature`, `builtin`).
- **Downstream uses:** Sigma-algebra closure and the left side of countable
  additivity.
- **Allowable hole:** None in the current module.

The dual `index_intersect(N+, Omega, family)` represents countable
intersection. `event_countable_intersection_is_event` proves its closure from
complement and countable-union closure; it is not an additional sigma-algebra
field.

### Real series sum

- **Ordinary meaning:** `L` is the limit of the finite partial sums of a real
  sequence.
- **Semantic role:** Candidate-value relation.
- **Ideal Litex form:** Recursive `partial_sum`, followed by `has_sequence_limit`
  and `has_series_sum` propositions.
- **Interface sketch:** `prop has_series_sum(a seq(R), L R)`.
- **Nearest wrong alternative:** An unconstrained `infinite_sum : seq(R) -> R`
  would pretend that every real series converges and would hide the analytic
  meaning of Kolmogorov's third axiom.
- **Dependencies:** Real arithmetic, absolute value, positive epsilons, and
  recursive sequences (`definition`, `well_definedness`).
- **Downstream uses:** Countable additivity of probability.
- **Allowable hole:** No selector for convergent series is needed in this
  module.

### Sigma-algebra

- **Ordinary meaning:** A family of subsets containing the empty and whole
  sample spaces and closed under relative complement, binary intersection,
  and countable union. Whole-space and binary-intersection closure are
  conservative projections of the smaller standard basis.
- **Semantic role:** Laws on supplied data, used as an ambient theorem context.
- **Ideal Litex form:** `setting SigmaAlgebraSetting(Omega, events)` with a
  definition-facing `prop is_sigma_algebra([SigmaAlgebraSetting])`.
- **Interface sketch:** `events power_set(power_set(Omega))` plus closure laws.
- **Nearest wrong alternative:** A `struct` would bundle proof fields into each
  value, while the construction needs an ordinary event family plus a flat,
  reusable law relation over candidate families.
- **Dependencies:** Countable union and native complement (`signature`, `law`).
- **Downstream uses:** Probability spaces, measurable maps, and event closure.
- **Allowable hole:** None. `generated_sigma_algebra<X>(generators)` constructs
  the intersection of all containing sigma algebras and proves its closure.

### Borel sigma algebra on the reals

- **Ordinary meaning:** The smallest sigma algebra on `R` containing every
  bounded open interval; this is the standard Borel sigma algebra.
- **Semantic role:** Constructed event family.
- **Ideal Litex form:** `borel_sigma_algebra_on_R =
  generated_sigma_algebra<R>(real_open_intervals)`.
- **Dependencies:** Generated sigma algebra and existential endpoint
  presentation of bounded open intervals (`definition`, `proof`).
- **Downstream uses:** Real-valued measurable maps and Borel probability laws.
- **Allowable hole:** General topological-space Borel generation is later work.

### Probability space

- **Ordinary meaning:** A sigma-algebra together with a nonnegative real-valued
  set function of total mass one that is countably additive on pairwise
  disjoint event sequences.
- **Semantic role:** Ambient law package on supplied data.
- **Ideal Litex form:** `setting ProbabilitySpaceSetting([SigmaAlgebraSetting],
  probability fn(A events) R)`.
- **Interface sketch:** nonnegativity, `probability(Omega) = 1`,
  `probability({}) = 0`, and the `has_series_sum` countable-additivity law.
- **Nearest wrong alternative:** A two-entry probability vector only models a
  finite distribution and duplicates the scope of showcase 8. A generic
  ENNReal-valued measure adds infinity machinery that probability spaces do
  not need because their total mass is one.
- **Dependencies:** Sigma-algebra, pairwise disjointness, and real series sums
  (`signature`, `law`).
- **Downstream uses:** Event probability, conditional probability,
  independence, and distributions.
- **Allowable hole:** The setting assumes a supplied probability function; it
  does not prove that every sigma-algebra admits one.

### Derived event-probability calculus

- **Ordinary meaning:** Countable additivity implies binary additivity on
  disjoint events; finite additivity then yields complement and difference
  formulas, monotonicity, inclusion-exclusion, the union bound, and the unit
  interval bound for every event probability.
- **Semantic role:** Theorem layer derived from the Kolmogorov setting.
- **Ideal Litex form:** A main theorem
  `probability_of_disjoint_union`, followed by small named consequences.
- **Interface sketch:** Pad `A` and `B` by empty events, identify the countable
  union with `A union B`, calculate the finite-support real series, and use
  uniqueness of series limits against countable additivity.
- **Nearest wrong alternative:** Adding finite additivity, complement laws, or
  monotonicity as new setting fields would obscure which facts are axioms and
  which are consequences.
- **Dependencies:** Countable additivity, empty-event probability, elementary
  set identities, finite-support series convergence, and uniqueness of real
  sequence limits (`proof`).
- **Downstream uses:** Conditional probability, countable subadditivity,
  continuity of probability, and probabilistic event-limit arguments.
- **Allowable hole:** General finite-family additivity is left as a natural
  induction exercise; the binary theorem already supports the ordinary
  formulas exposed in this checkpoint.

### Event tails, limsup, and liminf

- **Ordinary meaning:** The tail union contains points appearing in at least
  one event after a cutoff; the tail intersection contains points appearing in
  every event after a cutoff. Limsup means infinitely often and liminf means
  eventually always.
- **Semantic role:** Constructed measurable events.
- **Ideal Litex form:** Exact-carrier `have fn ... by exist!` definitions built
  from `index_union` and `index_intersect`.
- **Interface sketch:** `event_tail_union_after`,
  `event_tail_intersection_after`, `event_limsup`, and `event_liminf`.
- **Nearest wrong alternative:** Returning a raw subset of `Omega` would lose
  event membership and make later probability applications ill-defined.
- **Dependencies:** Sigma-algebra closure under countable unions and the
  derived countable-intersection theorem (`definition`, `well-definedness`).
- **Downstream uses:** Continuity from above and the first Borel--Cantelli
  lemma.
- **Allowable hole:** No two-sided convergence notion for arbitrary event
  sequences is introduced; limsup and liminf remain separately usable.

### Continuity and countable subadditivity

- **Ordinary meaning:** Probabilities of increasing events converge to the
  probability of their union, and probabilities of decreasing events converge
  to the probability of their intersection. The probability of a countable
  union is at most the sum of the event probabilities whenever that real
  series has a supplied sum.
- **Semantic role:** Derived theorem layer.
- **Ideal Litex form:** `probability_continuous_from_below`,
  `probability_continuous_from_above`, and
  `probability_countable_subadditivity` using relational sequence/series
  limits.
- **Nearest wrong alternative:** Adding continuity or subadditivity as
  probability-space fields would duplicate consequences of countable
  additivity.
- **Dependencies:** Disjointification of increasing sequences, complement
  duality, finite prefix union bounds, and uniqueness/order of real sequence
  limits (`proof`).
- **Downstream uses:** Tail-event estimates and Borel--Cantelli.
- **Allowable hole:** The series bound is deliberately conditional on a real
  sum candidate; no total infinite-sum selector is added.

### Null events, almost-sure events, and first Borel--Cantelli

- **Ordinary meaning:** Null events have probability zero; almost-sure events
  have probability one. If the sum of event probabilities converges, then the
  event that infinitely many of them occur is null.
- **Semantic role:** Relations and a derived limit theorem.
- **Ideal Litex form:** `is_null_event`, `is_almost_sure_event`, closure
  theorems, and `first_borel_cantelli`.
- **Nearest wrong alternative:** An unrestricted phrase such as "almost
  surely" without naming the event carrier and probability function would
  hide the exact probability space.
- **Dependencies:** Monotonicity, countable subadditivity, series-tail
  convergence, event limsup, and continuity from above (`proof`).
- **Downstream uses:** Later convergence-in-probability and almost-sure
  arguments.
- **Allowable hole:** Only the first Borel--Cantelli direction is present;
  the converse requires an independence hypothesis and is later work.

### Conditional probability and independence

- **Ordinary meaning:** `P(A | B) = P(A intersect B) / P(B)` for positive
  evidence, and `A`, `B` are independent when the numerator factors.
- **Semantic role:** Guarded function and relation.
- **Ideal Litex form:** `have fn conditional_probability(...) R` and
  `prop are_independent(...)`.
- **Interface sketch:** Both interfaces consume actual events from one
  `ProbabilitySpaceSetting`.
- **Nearest wrong alternative:** Treating conditional probability as a total
  function silently assigns a value when `P(B) = 0`.
- **Dependencies:** Probability space, native intersection, positivity, and
  real division (`signature`, `well_definedness`).
- **Downstream uses:** Bayes' rule and conditional independence.
- **Allowable hole:** Regular conditional probabilities are out of scope.

### Measurable map and random variable

- **Ordinary meaning:** A function is measurable when every measurable target
  set has a measurable preimage; a real random variable is such a map into a
  supplied sigma-algebra on `R`.
- **Semantic role:** Relations on two measurable spaces and a function.
- **Ideal Litex form:** `prop is_measurable_map(...)` and a specialized
  `prop is_random_variable(...)`.
- **Interface sketch:** A set-builder preimage belongs to the source
  sigma-algebra for every target event.
- **Nearest wrong alternative:** A random variable is not itself a probability
  measure and should not be encoded as a probability vector or distribution.
- **Dependencies:** Two sigma-algebras, functions, and set-builder preimages
  (`signature`, `definition`).
- **Downstream uses:** Pushforward distributions and, later, expectation.
- **Allowable hole:** Generic targets still supply their event family; for
  `Target = R`, the module provides `borel_sigma_algebra_on_R` explicitly.

### Pushforward probability measure

- **Ordinary meaning:** A target event receives the probability of its
  preimage under a measurable map.
- **Semantic role:** Constructed probability function, plus a relation exposing
  its distribution equation.
- **Ideal Litex form:** `pushforward_probability` together with
  `pushforward_probability_is_distribution` and
  `pushforward_probability_is_probability_space`.
- **Interface sketch:** For every target event `B`, its preimage is a source
  event and `distribution(B) = probability(X^{-1}(B))`.
- **Nearest wrong alternative:** A supplied candidate relation alone would not
  construct a function usable by later probability-space theorems; a random
  variable itself is not its distribution.
- **Dependencies:** Probability function, measurable preimages, and the target
  event family (`signature`, `definition`, `well-definedness`).
- **Downstream uses:** Target probability laws and later distributional
  expectation.
- **Allowable hole:** None for pushforward probability. Caratheodory extension
  from independent premeasure data remains out of scope.

### Concrete probability constructions

- **Ordinary meaning:** Dirac probability concentrates unit mass at one point;
  conditioning renormalizes intersection with positive-probability evidence;
  a finite atomic probability is a finite nonnegative weighted sum of Dirac
  probabilities with total weight one.
- **Semantic role:** Constructed functions with checked probability-space
  laws.
- **Ideal Litex form:** `dirac_probability`,
  `conditioned_probability_measure`, and `finite_atomic_probability`, each
  followed by a public `*_is_probability_space` theorem.
- **Nearest wrong alternative:** Merely asserting existence of a probability
  function would not expose a reusable value; making conditioning total would
  silently divide by zero.
- **Dependencies:** Event membership, positive evidence probability, scalar
  transport of convergent real series, finite-set sums, and Dirac countable
  additivity (`definition`, `well-definedness`, `proof`).
- **Downstream uses:** Direct model instances, conditional models, and finite
  discrete distributions.
- **Allowable hole:** These are probability constructions, not a general
  measure-extension theorem; no outer measure or integration is implied.

## Dependency map

Edge legend: `definition` means an interface unfolds to the dependency;
`law` means a setting requires the dependency; `signature` means the dependency
appears in a parameter or return carrier; `well-definedness` justifies a
guarded application; `proof` marks a named checked consumer.

```text
native sets + exact N+ set-valued families
  -> index_union(N+, Omega, family)               [builtin]
real arithmetic + epsilon limits
  -> partial_sum -> has_series_sum                [definition]

index_union + complement
  -> SigmaAlgebraSetting                          [law]
  -> index_intersect closure                      [proof]
  -> tail unions/intersections -> limsup/liminf   [definition, proof]
generator family + all containing sigma algebras
  -> generated_sigma_algebra                     [definition, proof]
bounded real open intervals + generated sigma algebra
  -> borel_sigma_algebra_on_R                    [definition, proof]
SigmaAlgebraSetting + has_series_sum
  -> ProbabilitySpaceSetting                      [law]
  -> countable-additivity tracer                  [proof]

finite-support sequences + uniqueness of limits
  -> two-term series sum                          [proof]
countable-additivity tracer + two-term series sum
  -> probability_of_disjoint_union                [proof]
  -> complement + difference                      [proof]
  -> monotonicity + inclusion-exclusion            [proof]
  -> union bound + 0 <= P(A) <= 1                 [proof]

increasing disjointification + countable additivity
  -> continuity from below                        [proof]
complement duality + continuity from below
  -> continuity from above                        [proof]
finite prefix unions + limit order
  -> countable subadditivity                      [proof]
series tails + tail unions + continuity from above
  -> first_borel_cantelli                         [proof]

ProbabilitySpaceSetting + intersection + P(B)>0
  -> conditional_probability                      [well-definedness]
ProbabilitySpaceSetting + intersection
  -> are_independent                              [definition]
  -> conditioned_probability_measure              [definition, proof]

point + SigmaAlgebraSetting
  -> dirac_probability                            [definition, proof]
finite nonnegative normalized weights + Dirac laws
  -> finite_atomic_probability                    [definition, proof]

source SigmaAlgebraSetting + target SigmaAlgebraSetting + preimage
  -> is_measurable_map                            [definition]
  -> is_random_variable                           [specialization]
ProbabilitySpaceSetting + is_measurable_map
  -> pushforward_probability                      [definition]
  -> is_distribution_of                           [proof]
  -> target probability space                     [proof]
```

There is no cycle. The only axiomatic boundary is the supplied setting data
and laws: no global Litex axiom, direct `trust`, or hidden selected measure is
part of the intended public file.

## Intended build order

Use the builtin indexed union first, then build partial sums and series
convergence, then the sigma-algebra setting and the generated-sigma
construction. Specialize it to Borel(R), then add the probability-space
setting and its direct
countable-additivity tracer. Next prove uniqueness of series sums and the
two-term finite-support series, then specialize countable additivity to obtain
binary finite additivity. Derive complement, difference, monotonicity,
inclusion-exclusion, the union bound, and the unit interval bound. Then derive
countable intersections, event tails, limsup/liminf, continuity from below and
above, and countable subadditivity. Null/almost-sure events and the first
Borel--Cantelli lemma consume that limit layer. Add event-level conditional
probability and independence, followed by the Dirac, conditioned, and finite
atomic probability constructions. Add measurable maps and the real-valued
random-variable specialization once both measurable spaces are available;
construct pushforward probability from measurable preimages and source
countable additivity.

## Interface decisions and permissible gaps

Preserve real-valued probability: normalization guarantees finiteness, so an
extended-nonnegative-real carrier would add machinery without improving this
module's semantics. Keep series summation relational, keep the positivity guard
on conditional probability, and keep a random variable distinct from its
pushforward distribution. The present measure construction is specifically a
pushforward from an existing probability space, while Dirac, positive-evidence
conditioning, and finite atomic sums are explicit special constructions. None
is a Caratheodory existence theorem. Expectation begins only after a genuine
integration interface exists.
