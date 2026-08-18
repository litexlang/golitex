# Mathematical Collections: Probability Theory

## Purpose and scope

This standalone module models the elementary measure-theoretic foundation of
probability through the Kolmogorov axioms. The source of truth is the standard
mathematical identity of a probability space `(Omega, events, probability)`:
`events` is a sigma-algebra on `Omega`, and `probability` is a nonnegative,
normalized, countably additive real-valued set function. The first checkpoint
includes event operations, conditional probability, independence, measurable
maps, real-valued random variables, and pushforward distributions. It excludes measure construction,
Lebesgue/Borel generation, integration, expectation, laws of large numbers,
and limit theorems.

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

Settings carry theorem-wide ambient data and laws. They do not construct a
sigma-algebra or a probability measure. The sigma-algebra setting exposes the
whole-space and binary-intersection laws, and the probability setting exposes
the empty-event zero law, even though all three are derivable from smaller
axiom bases; these are conservative, standard projection laws that make the
public interface usable without changing its models.

## Mathematical spine

### Countable union

- **Ordinary meaning:** The subset containing exactly the points that occur in
  at least one set of a positive-natural-indexed family.
- **Semantic role:** Set-valued construction.
- **Ideal Litex form:** A membership `prop` plus a templated `have fn` returning
  `power_set(Omega)`.
- **Interface sketch:**
  `countable_union(family fn(n N+) power_set(Omega)) power_set(Omega)`.
- **Nearest wrong alternative:** Leaving only an existential membership
  relation would force every sigma-algebra and probability caller to rebuild
  the resulting set.
- **Dependencies:** Native sets, functions, existential witnesses, and set
  builders (`signature`, `definition`).
- **Downstream uses:** Sigma-algebra closure and the left side of countable
  additivity.
- **Allowable hole:** None in the first checkpoint.

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
- **Nearest wrong alternative:** A `struct` would force projections although
  the first checkpoint never stores, returns, or compares sigma-algebra values.
- **Dependencies:** Countable union and native complement (`signature`, `law`).
- **Downstream uses:** Probability spaces, measurable maps, and event closure.
- **Allowable hole:** Generating a sigma-algebra from a family is later work.

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
- **Allowable hole:** The Borel sigma-algebra is supplied rather than
  constructed in the first checkpoint.

### Pushforward distribution

- **Ordinary meaning:** A target event receives the probability of its
  preimage under a measurable map.
- **Semantic role:** Relation on a supplied candidate distribution.
- **Ideal Litex form:** `prop is_distribution_of(...)`.
- **Interface sketch:** For every target event `B`, its preimage is a source
  event and `distribution(B) = probability(X^{-1}(B))`.
- **Nearest wrong alternative:** A total selected distribution constructor
  would hide the existence, measurability, and probability-space obligations;
  a random variable itself is not its distribution.
- **Dependencies:** Probability function, measurable preimages, and the target
  event family (`signature`, `definition`, `well-definedness`).
- **Downstream uses:** `distribution_of_has_measurable_map` and later
  distributional expectation.
- **Allowable hole:** Existence and uniqueness of a probability-space-valued
  pushforward construction remain separate future results.

## Dependency map

Edge legend: `definition` means an interface unfolds to the dependency;
`law` means a setting requires the dependency; `signature` means the dependency
appears in a parameter or return carrier; `well-definedness` justifies a
guarded application; `proof` marks a named checked consumer.

```text
native sets + N+ families
  -> countable_union                              [definition]
real arithmetic + epsilon limits
  -> partial_sum -> has_series_sum                [definition]

countable_union + complement
  -> SigmaAlgebraSetting                          [law]
SigmaAlgebraSetting + has_series_sum
  -> ProbabilitySpaceSetting                      [law]
  -> countable-additivity tracer                  [proof]

ProbabilitySpaceSetting + intersection + P(B)>0
  -> conditional_probability                      [well-definedness]
ProbabilitySpaceSetting + intersection
  -> are_independent                              [definition]

source SigmaAlgebraSetting + target SigmaAlgebraSetting + preimage
  -> is_measurable_map                            [definition]
  -> is_random_variable                           [specialization]
ProbabilitySpaceSetting + is_measurable_map
  -> is_distribution_of                           [definition]
  -> distribution_of_has_measurable_map           [proof]
```

There is no cycle. The only axiomatic boundary is the supplied setting data
and laws: no global Litex axiom, direct `trust`, or hidden selected measure is
part of the intended public file.

## Intended build order

Build countable unions first, then partial sums and series convergence, then
the sigma-algebra setting, the probability-space setting, and its direct
countable-additivity tracer. Add event-level conditional probability and
independence only after that foundation. Add measurable maps and the
real-valued random-variable specialization next, because they consume two
already-defined measurable spaces. Add the pushforward-distribution relation
last so it can reuse measurable preimages and the source probability.

## Interface decisions and permissible gaps

Preserve real-valued probability: normalization guarantees finiteness, so an
extended-nonnegative-real carrier would add machinery without improving this
module's semantics. Keep series summation relational, keep the positivity guard
on conditional probability, and keep a random variable distinct from its
pushforward distribution. Expectation begins only after a genuine integration
interface exists; finite weighted sums remain in showcase 8 rather than being
presented here as general measure-theoretic expectation.
