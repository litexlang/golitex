# Mathematical Collections

## Purpose and scope

This module formalizes the non-exercise mathematical content of Chapters 1
through 3 of *Concrete Mathematics: A Foundation for Computer Science*. The
authoritative source is the repository-local transcript locked in the paired
workspace's `source_manifest.yaml`. Chapter 1 contributes recursive
definitions and their closed forms. Chapter 2 contributes finite summation
objects and laws, recurrence-to-sum transformations, finite calculus, and the
source's convergence criteria for infinite sums.

Standalone exercises are excluded. OCR artifacts in the transcript are source
quality issues and must be resolved before a source statement is modeled; they
are not Litex failures. The intended downstream users are readers learning
how ordinary recurrence and summation mathematics maps to Litex, and future
skill authors mining repeated formalization mistakes.

## Modeling conventions

- Natural-number indices use builtin `N`; strictly positive indices use
  builtin `N+` when zero is mathematically excluded.
- A recursively defined sequence is a callable `have fn`, normally with
  `by induc` or `by cases`. A proposition describing its graph is not an
  acceptable substitute.
- Finite interval sums use builtin `sum(first, last, f)`. Sums over a genuine
  finite set use `finite_set_sum(S, f)`.
- Source notation such as `T_n`, `L_n`, `S_n`, and `J(n)` becomes a callable
  named function. Source equations remain source-facing theorems or direct
  checked facts when they are mathematically significant.
- Geometry needed only to motivate a recurrence is not silently promoted into
  a full Euclidean-geometry library. The recurrence and its upper/lower-bound
  justification stay visible, with any unavailable geometry isolated as an
  exact proof boundary.
- Infinite sums are not represented by finite `sum`. Their ideal interface
  retains the source's bounded-finite-subsums or limit semantics; an
  unsupported selected value must remain visibly blocked rather than being
  encoded as a finite aggregate.

## Mathematical spine

### Tower-of-Hanoi move count

- **Ordinary meaning:** `hanoi_moves(n)` is the minimum number of legal moves
  needed to transfer a tower of `n` disks.
- **Semantic role:** Function.
- **Ideal Litex form:** Recursive `have fn`.
- **Interface sketch:** `have fn hanoi_moves(n N) N by induc n from 0: ...`
- **Nearest wrong alternative:** A `prop hanoi_recurrence(n, value)` would
  force every later theorem to carry a candidate value instead of applying
  `hanoi_moves(n)`.
- **Dependencies:** `N` by signature; the recursive rule by definition; the
  minimality interpretation has a geometry/puzzle proof dependency.
- **Downstream uses:** Recurrence (1.1), closed form (1.2), and the shifted
  sequence in (1.3). Probe: `hanoi_moves(3) = 7`.
- **Allowable hole:** The recurrence itself is checked. The builtin
  predecessor carrier rule discharges `n - 1 : N` in the positive branch;
  only the puzzle-minimality interpretation may remain a separate proof
  boundary.

### Planar-region maximum

- **Ordinary meaning:** `line_regions(n)` is the largest number of regions
  determined by `n` straight lines in the plane.
- **Semantic role:** Function.
- **Ideal Litex form:** Recursive `have fn`, with source-facing recurrence and
  closed-form theorems.
- **Interface sketch:** `line_regions(0)=1` and
  `line_regions(n+1)=line_regions(n)+(n+1)`.
- **Nearest wrong alternative:** A relation about an arbitrary proposed
  region count would not expose the numerical sequence used later.
- **Dependencies:** `N` by signature; the line-arrangement argument by proof;
  triangular sums by definition/proof.
- **Downstream uses:** Equations (1.4), (1.6), and comparison with bent-line
  regions. Probe: `line_regions(3) = 7`.
- **Allowable hole:** Realizing the maximum by a general-position line
  arrangement may be trusted narrowly if the current geometry surface cannot
  express it. The numerical recurrence and its exact base/step interface are
  checked directly.

### Triangular-number sum

- **Ordinary meaning:** `triangular_sum(n)` is the sum of the integers from
  `1` through `n`.
- **Semantic role:** Formula-defined function.
- **Ideal Litex form:** `have fn` backed by builtin `sum`, with a named
  source-facing closed-form theorem.
- **Interface sketch:**
  `have fn triangular_sum(n N) N = sum(1,n,fn(k Z) Z {k})`, subject to the
  exact result carrier verified by a probe.
- **Nearest wrong alternative:** A proposition asserting that a candidate is
  a triangular number would not support evaluation or later substitution.
- **Dependencies:** Builtin `sum` by definition; induction or reversal by
  proof.
- **Downstream uses:** Equations (1.5), (1.6), and Chapter 2 recurrence/sum
  conversions. Probe: `triangular_sum(4) = 10`.
- **Allowable hole:** The exact carrier bridge between integer-range `sum`
  and an `N`-valued public function must be verified before freezing the
  signature.

### Josephus survivor

- **Ordinary meaning:** `josephus_survivor(n)` is the surviving label when
  every second remaining person is eliminated from a circle of `n` people.
- **Semantic role:** Function on positive natural numbers.
- **Ideal Litex form:** Recursive `have fn` with even/odd cases.
- **Interface sketch:** Base value at `1`, then
  `J(2*n)=2*J(n)-1` and `J(2*n+1)=2*J(n)+1`.
- **Nearest wrong alternative:** A `prop` relating `n` to a survivor hides the
  callable sequence and makes iteration awkward.
- **Dependencies:** `N+` by signature; parity and decreasing recursive
  arguments by well-definedness; elimination reasoning by proof.
- **Downstream uses:** Equations (1.8)--(1.10), iteration, and generalized
  radix recurrences. Probe: `josephus_survivor(10) = 5`.
- **Allowable hole:** The circle-elimination interpretation may retain narrow
  proof debt; the recursive function must remain executable and typed.

### General binary and radix recurrences

- **Ordinary meaning:** These families evaluate a number digit by digit, with
  a base case for the leading digit and an affine recurrence for appended
  digits.
- **Semantic role:** Parameterized callable functions and source-facing
  results.
- **Ideal Litex form:** `have fn` parameterized by constants; use `template`
  only if a reusable declaration family is actually instantiated by callers.
- **Interface sketch:** Equation (1.11)'s `f(1)`, `f(2*n)`, and
  `f(2*n+1)` cases, followed by equation (1.17)'s radix-`d` form.
- **Nearest wrong alternative:** A template merely because the recurrence has
  parameters would inflate an ordinary mathematical function family into a
  declaration family.
- **Dependencies:** Josephus recurrence by generalization; digit/radix
  representations by signature and proof.
- **Downstream uses:** Repertoire method and equations (1.12)--(1.18).
- **Allowable hole:** A general digit-sequence representation may be isolated
  as an exact library or proof boundary if no natural builtin surface exists.

### Finite interval sum

- **Ordinary meaning:** The sum of an indexed numeric function over a closed
  integer interval.
- **Semantic role:** Builtin function.
- **Ideal Litex form:** Builtin `sum(first, last, f)`.
- **Interface sketch:** `sum(1, n, fn(k Z) Z {k})`.
- **Nearest wrong alternative:** Rebuilding Sigma notation as a new recursive
  proposition or treating all sums as finite-set sums duplicates the builtin
  interface and loses ordered bounds.
- **Dependencies:** Integer bounds and numeric function codomain by
  well-definedness.
- **Downstream uses:** Chapter 2's recurrence identity, index shifts,
  perturbation, finite calculus, and closed forms.
- **Allowable hole:** General predicate-indexed source sums may require a
  finite-set formulation or an explicitly characterized finite support.

### Sum transformations

- **Ordinary meaning:** Linearity, range splitting, index substitution, and
  exchange of finite summation order preserve the value of a sum.
- **Semantic role:** Reusable results, with direct builtin facts preferred
  when available.
- **Ideal Litex form:** Direct facts or named `thm` only for source-numbered
  reusable results.
- **Interface sketch:** Equations (2.15)--(2.35), expressed using `sum`,
  `finite_set_sum`, ranges, Cartesian products, and callable functions.
- **Nearest wrong alternative:** Trusted wrapper theorems around facts already
  discharged by builtin rules obscure the actual Litex surface.
- **Dependencies:** Finite sums by signature; bijections/permutations and
  finite sets by proof.
- **Downstream uses:** Arithmetic/geometric sums, multiple sums, and Chapter
  2's general methods.
- **Allowable hole:** A transformation unsupported in the current API may
  remain a narrow source theorem debt after one direct real-context probe.

### Finite difference and factorial powers

- **Ordinary meaning:** `delta(f)(x)=f(x+1)-f(x)` is the discrete derivative;
  falling and rising powers are product-defined polynomial-like functions
  adapted to it.
- **Semantic role:** Higher-order function and formula-defined functions.
- **Ideal Litex form:** `have fn` declarations, plus source-facing theorems.
- **Interface sketch:** Equations (2.42)--(2.56).
- **Nearest wrong alternative:** Props describing candidate outputs prevent
  later code from applying `delta`, falling powers, or antidifferences.
- **Dependencies:** Function sets, products, finite sums, and algebra by
  signature/definition/proof.
- **Downstream uses:** Finite-calculus summation formulas and the square-sum
  derivation.
- **Allowable hole:** Negative falling powers and indefinite-sum equivalence
  may expose exact domain or library gaps without weakening the functions.

### Infinite sum and absolute convergence

- **Ordinary meaning:** A nonnegative family sum is the least upper bound of
  its finite subsums; a signed or complex family sum is defined through
  positive/negative or real/imaginary parts when absolute convergence
  permits it.
- **Semantic role:** Candidate-value relation, convergence property, and
  possibly a canonical selected value after uniqueness.
- **Ideal Litex form:** Real relations first; a selected `have fn ... by
  exist!` only after existence and uniqueness are available.
- **Interface sketch:** Source equations (2.58)--(2.59) and the finite-subsum
  boundedness condition.
- **Nearest wrong alternative:** Encoding an infinite sum with finite `sum`
  changes the mathematics; exposing a selected value before convergence and
  uniqueness hides the defining obligation.
- **Dependencies:** Finite subsets and finite sums by definition; real
completeness by existence; order independence by proof.
- **Downstream uses:** Infinite geometric series and exchange of absolutely
  convergent double sums.
- **Allowable hole:** Completeness, arbitrary-index finite subsums, or complex
  decomposition may remain explicit proof/library boundaries.

### Floor, ceiling, and fractional part

- **Ordinary meaning:** `floor(x)` is the greatest integer at most `x`,
  `ceil(x)` is the least integer at least `x`, and `fractional_part(x)` is
  `x-floor(x)`.
- **Semantic role:** The first two are builtin functions; fractional part is a
  formula-defined function. Source-numbered characterization, shift,
  reflection, and comparison laws are reusable results.
- **Ideal Litex form:** Reuse builtin `floor` and `ceil`; introduce
  `have fn fractional_part(x R) R = x - floor(x)` and source-facing theorems.
- **Nearest wrong alternative:** New props describing candidate rounded
  integers would duplicate the callable builtins and make later applications
  carry witnesses.
- **Dependencies:** `R` and `Z` by signature; native rounding bounds and
  integer-fixing rules by proof; discreteness of `Z` for the converse
  characterization laws.
- **Downstream uses:** Floor/ceiling applications, recurrences, `mod`, and
  floor sums throughout Chapter 3. Probes include `floor(2.75)=2`,
  `ceil(-2.75)=-2`, and `0 <= fractional_part(x) < 1`.
- **Allowable hole:** None in Section 3.1. The gap, characterizations,
  reflections, integer shifts, comparison equivalences, and fractional-part
  bounds are checked using native rounding facts plus integer adjacency.

### Binary digit length

- **Ordinary meaning:** A positive integer `n` has
  `floor(log(2,n))+1` binary digits.
- **Semantic role:** Callable positive-natural count.
- **Ideal Litex form:** `have fn ... by exist!` from `N+` to `N+`, selecting
  the unique value equal to the source formula.
- **Nearest wrong alternative:** Returning the formula in `N` or `Z` loses the
  fact that every positive integer has at least one digit.
- **Dependencies:** The builtin sign rule for logarithms with base greater than
  one, the floor comparison theorem, and unique selection.
- **Downstream uses:** Binary/radix recurrence descriptions and the concrete
  probe `binary_digit_length_39(8)=4`.
- **Allowable hole:** None. The unit input evaluates directly; the strict
  branch proves the rounded logarithm nonnegative and the final count positive.

### Square-root and nested-quotient rounding laws

- **Ordinary meaning:** On nonnegative inputs, floor and ceiling commute with
  square root; an inner floor or ceiling may also be absorbed before division
  by a positive integer.
- **Semantic role:** Source-facing theorems (3.9) and (3.11).
- **Ideal Litex form:** Checked `thm` declarations over native `floor`, `ceil`,
  and `sqrt`, preserving the source domains `x R`, `m Z`, and `n N+`.
- **Dependencies:** Rounding characterizations and integer adjacency by proof;
  square-root nonnegativity/monotonicity and positive division by builtin.
- **Downstream uses:** Root rounding, quotient normalization, and later floor
  sums in Chapter 3.
- **Allowable hole:** None. The root laws transfer squared integral bounds
  through floor/ceiling; the quotient laws multiply by `n`, use adjacency at
  an integral endpoint, and divide back explicitly.

### Rounding-compatible increasing maps

- **Ordinary meaning:** A strictly increasing map with the intermediate-value
  property and no noninteger preimages of integers commutes with floor and
  ceiling as stated in (3.10).
- **Semantic role:** Source-facing predicate plus checked theorem.
- **Ideal Litex form:** Keep the direct interval-witness predicate used by the
  chapter; do not introduce a broader continuity hierarchy solely for this use.
- **Dependencies:** Strict monotonicity, integer preimages, intermediate-value
  witnesses, and the checked floor/ceiling endpoint characterizations.
- **Downstream uses:** Moving floor or ceiling through suitable increasing
  functions in later rounding calculations.
- **Allowable hole:** None. If a rounded output lay strictly between the two
  endpoint images, its preimage would be an integer in a one-unit rounding
  interval, hence the relevant endpoint, contradicting strict separation.

### Integer counts in real intervals

- **Ordinary meaning:** Each interval-count function returns the number of
  integers in one of the four real intervals `[alpha,beta]`,
  `[alpha,beta)`, `(alpha,beta]`, or `(alpha,beta)` under the source's stated
  endpoint condition.
- **Semantic role:** Canonical count-valued functions.
- **Ideal Litex form:** `have fn ... by exist!` into `N`, selecting the unique
  natural value equal to each source formula in (3.12).
- **Interface sketch:**
  `closed_open_interval_integer_count(alpha R, beta R: alpha <= beta) N`.
- **Nearest wrong alternative:** A `Z`-valued formula alone is not the actual
  cardinality object and permits negative outputs outside the source domain.
- **Dependencies:** Floor/ceiling comparisons and integer adjacency prove the
  integral formulas nonnegative; unique selection supplies the callable
  natural-valued functions.
- **Downstream uses:** The casino winner count and later floor-sum lattice
  counts. Probe: the integers in `[1.2,4.2)` number `3`.
- **Allowable hole:** None for the implemented formula interfaces. A separate
  finite-set cardinality realization would be an alternate construction, not
  a prerequisite for using the source's four checked count formulas.

### Casino winner count

- **Ordinary meaning:** `casino_winner_count(N)` counts positive integers at
  most `N` that are divisible by the floor of their cube root.
- **Semantic role:** Count-valued function, with a source closed-form theorem.
- **Ideal Litex form:** A source winner `prop`, then `have fn` into `N` as the
  cardinality of its filtered finite range. Keep the positive cube-block index
  existential inside the winner relation until a reusable selector has an
  independent consumer.
- **Interface sketch:** Equation (3.13) with
  `K=floor(N^(1/3))` and the source formula for `W`.
- **Nearest wrong alternative:** Returning the algebraic right-hand side in
  `R` or `Z` changes the meaning of a finite count.
- **Dependencies:** Positive integers and divisibility by definition;
  half-open interval counts and finite sums by proof.
- **Downstream uses:** The 1000-slot casino probe `W=172` and asymptotic
  discussion later in the chapter.
- **Allowable hole:** Only the generic finite-cardinality decomposition that
  partitions the filtered range into complete cube blocks and one final block.
  The winner relation, N-valued count object, final polynomial simplification,
  and `W(1000)=172` consumer are checked.

### Spectrum sequence and prefix count

- **Ordinary meaning:** The spectrum of positive `alpha` is the sequence
  `floor(k*alpha)` for positive indices `k`; its prefix count records how many
  terms are at most a natural bound `n`.
- **Semantic role:** Callable sequence and canonical count-valued function.
- **Ideal Litex form:**
  `have fn spectrum(alpha R+, k N+) Z = floor(k*alpha)` plus an `N`-valued
  prefix-count function satisfying equation (3.14).
- **Nearest wrong alternative:** A membership prop loses multiplicity and
  order, so it cannot represent the source's multiset or support prefix
  counts.
- **Dependencies:** Native floor by definition; integer interval counts,
  irrationality of `sqrt(2)`, and the adjacency law (3.15) by proof.
- **Downstream uses:** The spectra of `sqrt(2)` and `2+sqrt(2)` and their
  partition-count identity.
- **Allowable hole:** None for the checked sequence, N-valued prefix-count
  formula, reciprocal identity, nonintegral quotient argument, or final
  partition count. Only the foundational fact `sqrt(2) notin Q` remains
  localized; the Beatty/floor/ceiling proof itself is checked.

### Rounded recurrences and generalized Josephus thresholds

- **Ordinary meaning:** Knuth and merge recurrences call earlier values at
  rounded smaller indices. The generalized Josephus answer is selected from
  the first threshold `D_k>(q-1)n`, with
  `D_0=1` and `D_k=ceil(q*D_(k-1)/(q-1))`.
- **Semantic role:** Callable sequences, typed rounded-index helpers, a
  least-index predicate, and a selected survivor value.
- **Ideal Litex form:** Preserve `N`/`N+` carriers; expose rounded indices and
  the nonzero denominator as local mathematical helpers; state minimality as
  a prop and selection as `have fn`/`have fn by exist!` when available.
- **Nearest wrong alternative:** Weakening every rounded index to `Z`, or
  adding a Knuth/Josephus-specific kernel rule, hides the actual carrier and
  termination obligations.
- **Dependencies:** Floor/ceil and integer adjacency by proof; refined carrier
  propagation by well-definedness; first-threshold existence and uniqueness
  by selection.
- **Downstream uses:** The source recurrences (3.16)--(3.20) and the q=2
  threshold probe.
- **Allowable hole:** None for the checked N-valued floor quotient, integer
  half-split identity, positive half selectors, Josephus denominator,
  N+-valued threshold recurrence, strict growth, `D_k>=k+1`, least-index and
  survivor selections, or the Knuth/merge recurrences. All Section 3.3 source
  carriers and recursive equations are checked; none uses an object-specific
  kernel rule.

### Total real remainder

- **Ordinary meaning:** For `y!=0`, `x mod y=x-y*floor(x/y)`; the source makes
  it total by defining `x mod 0=x`.
- **Semantic role:** A case-defined binary function with sign bounds, scaling,
  and finite floor-distribution theorems.
- **Ideal Litex form:** `have fn ... by cases`, followed by ordinary theorems.
  Divisor-zero behavior belongs in this definition, not in the builtin `%`
  operation or a special verifier branch.
- **Nearest wrong alternative:** Reusing integer `%` changes both the domain
  and the source's zero-divisor convention.
- **Dependencies:** Native floor bounds and real ordered-field algebra.
- **Downstream uses:** Equations (3.21)--(3.26) and later floor sums.
- **Allowable hole:** None for equations (3.21)--(3.26). The scaling law is
  checked by cases and quotient cancellation. The partition identities use
  quotient/remainder bounds and finite-range splitting; floor distribution
  additionally uses nested-floor absorption and integer-shift reindexing. A
  slow replay is not an allowable proof hole.

### Discrepancy and gcd floor sums

- **Ordinary meaning:** `discrepancy_sum_329` measures deviation of fractional
  parts from uniform distribution; `discrepancy_329` is its maximum over the
  unit interval. The final floor progression has a gcd-dependent closed form
  and is symmetric in its positive integer parameters.
- **Semantic role:** Checked finite sums and indicators, semantic maximum and
  analysis interfaces, bounded error objects, and source-facing theorems.
- **Ideal Litex form:** Define the epsilon/cutoff limit predicate, indicator,
  finite sums, transformed variables, and gcd reciprocity in Litex. Equation
  (3.27)'s square-root prefix sum is checked by induction. Model (3.29) by a
  maximum predicate and unique choice; trust only maximum existence, the
  absent a.e.-continuity/integral semantics, boundary-error selection, and the
  advanced source theorems.
- **Nearest wrong alternative:** An empty `abstract_prop` for convergence or a
  trusted reciprocity theorem would discard definitions and proofs that Litex
  can already express.
- **Dependencies:** Chapter 2's empty-sum wrapper, fractional part, real
  absolute value/order, native gcd facts, and external integration theory.
- **Downstream uses:** Equations (3.27)--(3.32), including the checked final
  reciprocity law.
- **Allowable hole:** Compact maximum existence, a.e. integration, boundary
  correction selection, and the remaining exact advanced closed forms may
  remain explicitly itemized trust debt. The maximum's uniqueness and public
  laws, plus all natural-valued rounded carriers, are checked and are not
  allowable holes.

## Dependency map

Edge legend: `signature` selects carriers and function sets; `definition`
unfolds to a prerequisite; `well_definedness` justifies an application;
`proof` supplies a theorem; `existence`, `uniqueness`, and `selection` govern
canonical values; `trust/source` marks explicit proof debt.

```text
N, N+, Z and callable functions
  --signature--> recursive sequences
positive branch + predecessor builtin
  --well_definedness--> N and N+ predecessor recurrences

hanoi_moves
  --proof--> Hanoi recurrence (1.1)
  --proof--> Hanoi closed form (1.2)

builtin sum
  --definition--> triangular_sum
  --proof--> triangular closed form (1.5)
triangular_sum
  --proof--> line_regions closed form (1.6)

parity + decreasing positive arguments
  --well_definedness--> josephus_survivor
josephus_survivor
  --proof--> power-of-two form (1.9)
  --proof--> binary rotation (1.10)
  --definition/generalization--> affine binary recurrence (1.11)
affine binary recurrence
  --proof--> radix recurrence (1.17) and digit solution (1.18)

finite set-builder over closed_range(0, (q-1)n)
  --well_definedness--> N-valued least Josephus threshold index
least Josephus threshold index + threshold recurrence
  --proof--> N+-valued generalized Josephus survivor (3.19)--(3.20)

builtin sum + finite_set_sum
  --definition--> finite summation vocabulary
finite summation vocabulary
  --proof--> sum transformations
  --definition--> recurrence/sum conversion
  --definition--> finite calculus

finite subsums + real completeness
  --existence--> nonnegative infinite-family sums
nonnegative sums + positive/negative decomposition
  --definition--> absolute convergence and signed sums
absolute convergence
  --proof--> order-independent double summation

builtin floor/ceil characteristic bounds
  --definition--> fractional_part
  --proof + integer adjacency--> floor/ceiling characterizations and transformations
floor/ceiling transformations
  --proof + sqrt monotonicity--> root commutation (3.9)
  --proof + integer preimage/interval witness--> compatible-map commutation (3.10)
  --proof + integer adjacency--> nested quotients (3.11)
checked rounding applications
  --proof--> Chapter 3 recurrences, mod, and sums
integer interval subsets + cardinality
  --selection--> interval integer counts
floor/ceiling comparisons
  --proof--> interval count formulas
interval counts + finite sums
  --proof--> casino_winner_count
native floor
  --definition--> spectrum
interval counts + integer adjacency
  --proof--> spectrum prefix count
spectrum prefix count
  --proof--> sqrt(2) spectrum partition counts

rounded-index carrier helpers
  --well_definedness--> Knuth and merge recurrence interfaces
positive q predecessor + threshold selection
  --selection--> generalized Josephus survivor

floor characteristic bounds
  --definition--> total real remainder
total real remainder + finite sums
  --proof--> rounded partitions and floor distribution

fractional part + real Iverson indicator
  --definition--> finite discrepancy sum
unit-interval maximum existence + upper-bound/attainment predicate
  --existence/uniqueness/selection--> discrepancy
discrepancy + boundary correction
  --proof--> transformed discrepancy recurrence
native gcd facts + finite integer sums
  --proof--> floor-progression closed form and reciprocity

geometric line realization
  --trust/source?--> line_regions recurrence
circle-elimination interpretation
  --trust/source?--> Josephus recurrence
```

## Intended build order

1. Verify carrier and recursion probes for natural-number functions.
2. Implement the Hanoi sequence and its algebraic closed form.
3. Verify interval-sum carrier behavior and implement triangular numbers.
4. Implement planar-region numerical recurrences; isolate geometry only if
   the real-context probe requires it.
5. Implement the Josephus function, closed form, and binary consequences.
6. Implement the generalized binary/radix recurrence interfaces.
7. Establish Chapter 2's finite-sum vocabulary and recurrence bridge.
8. Add finite-sum transformations and multiple-sum results in source order.
9. Add square-sum methods and finite-calculus functions/results.
10. Model infinite sums through finite subsums and convergence, keeping
    completeness and selection boundaries visible.
11. Reuse native floor/ceiling interfaces, then add fractional part and the
    source's characterization laws before Chapter 3 applications.
12. Add rounding applications, exact interval count objects, the casino count,
    and spectrum/prefix-count interfaces in Section 3.2 source order.
13. Add typed rounded-index helpers and callable recurrence/threshold
    interfaces for Section 3.3.
14. Define total real remainder by cases, then add the partition and
    floor-distribution theorems in Section 3.4.
15. Define square-root and discrepancy sums before adding the analytic and
    gcd closed forms of Section 3.5; derive reciprocity from the gcd form.

This order follows the source except that the reusable triangular-sum function
is stabilized before the planar closed form that consumes it.

## Interface decisions and permissible gaps

- Recursive sequences remain callable functions even if their combinatorial
  interpretations are not fully formalized.
- `sum` and `finite_set_sum` keep distinct interval-versus-set meanings.
- General parameters do not by themselves justify `template`.
- Infinite sums are never approximated by a finite aggregate merely to obtain
  checkable code.
- Geometry, completeness, or digit-representation debt may be trusted only at
  the smallest source-facing proof step after a direct probe; no such debt may
  alter a carrier, function boundary, or theorem conclusion.
