# Mathematical Collections

> Publication status (2026-08-21): the runnable module exports the recovered
> shared cite interfaces and all Chapters 1--20. The sequence, derivative,
> counting, distribution, regression, and independence cards below are current
> registered interfaces rather than quarantined drafts.

## Purpose and scope

This module covers the 20 concept-level high-school curriculum units in
`scripts/high_school_book/knowledge_core_json/index.json`. The local JSON
summaries, not any external textbook prose, are the source of truth. The book
includes definitions, reusable interfaces, representative theorems, small
checked examples, and one original exercise companion for each of the eleven
mathematical directions. External exercise prose, source answer keys, and long
textbook explanations are excluded.

## Modeling conventions

- Native carriers `N`, `Z`, `Q`, `R`, and `C` carry their standard scalar
  meaning; real or complex structure is not rebuilt as a predicate.
- A named construction used by application is a `have fn`, including lines,
  circles, conics, coordinate operations, rates, and finite statistics.
- Candidate conditions such as being a root, circle, stationary point,
  parallel pair, or finite sample space are `prop` relations.
- Canonical circle centers are exposed by `have fn ... by exist!` only after
  the unique-center relation is available.
- Native trigonometry and native complex coordinates are used directly. The
  former custom `struct C` is deliberately not preserved under an alias.
- Substantial omitted mathematics is isolated in `HighSchoolCite`; `trust` is
  a visible epistemic boundary, never the semantic form of a concept.

## Mathematical spine

### Sets and logical relations

- **Ordinary meaning:** Membership, subset, proper subset, finite set
  operations, implication, cases, and contradiction.
- **Semantic role:** Builtin carriers and operations, including the native
  `$proper_subset` relation.
- **Ideal Litex form:** Native `$proper_subset` plus source-facing set-law
  results.
- **Interface sketch:** `A $proper_subset B`.
- **Nearest wrong alternative:** A new set structure would duplicate native
  membership and subset interfaces.
- **Dependencies:** Native sets and logic; set-lattice proofs use
  `HighSchoolCite::sets`.
- **Downstream uses:** Chapter 1 and finite probability/statistics chapters.
- **Allowable hole:** None for the set-lattice and set-difference identities
  used by this book; those shared results are checked extensionally.

### Real functions and inverse relations

- **Ordinary meaning:** Real functions classified by parity, monotonicity,
  extrema, zeros, inverse behavior, and graphs.
- **Semantic role:** Functions are `have fn`; classifications are `prop`;
  inverse existence is a theorem.
- **Ideal Litex form:** `prop strictly_increasing_fn(f fn(x R) R)` and
  `have fn graph_of(f ...) power_set(cart(R, R))`.
- **Nearest wrong alternative:** A predicate standing in for `graph_of(f)`
  would prevent later set membership and graph reflection.
- **Dependencies:** Real order, function ranges, set builders, unique
  preimages, continuity.
- **Downstream uses:** Chapters 3, 4, 6, and 17.
- **Allowable hole:** The intermediate-value theorem may remain cited proof
  debt. Inverse selection on `fn_range` and inverse-graph reflection should be
  checked from unique preimages rather than treated as background.

### Trigonometric functions

- **Ordinary meaning:** Radian angles, sine, cosine, tangent, secant, identities,
  periods, ranges, and transformed sine curves.
- **Semantic role:** Native symbolic functions plus the source-facing
  `secant`, `deg`, `transformed_sine`, and measurement functions.
- **Ideal Litex form:** `have fn secant(theta R: cos(theta) != 0) R = 1 / cos(theta)`.
- **Nearest wrong alternative:** A compatibility theorem namespace for builtin
  identities would duplicate the current native trigonometric interface.
- **Dependencies:** `pi`, real arithmetic, and the tangent denominator facts.
- **Downstream uses:** Chapters 5, 6, 10, and 14.
- **Allowable hole:** Complex trigonometry and unsupported special-angle
  evaluations are outside the module.

### Coordinate vectors and analytic geometry

- **Ordinary meaning:** Coordinate addition, scalar multiplication, dot
  products, norms, lines, circles, conics, spatial directions, and incidence.
- **Semantic role:** Coordinate operations and geometric loci are `have fn`;
  incidence and classification conditions are `prop`.
- **Ideal Litex form:** `have fn circle_center(h, k R, r R+) power_set(cart(R, R)) = ...`,
  with coordinate planes and lines represented by set builders over
  `cart(R, R, R)` and direction criteria represented by dot-product `prop`s.
- **Nearest wrong alternative:** A relation-only circle interface would make a
  circle unusable as a set in intersection and tangent statements.
- **Dependencies:** Cartesian products, set builders, real algebra, square
  roots, unique existence for `center_of_circle`.
- **Downstream uses:** Chapters 7, 9, 10, 13, 14, and 15.
- **Allowable hole:** General synthetic 3D incidence is outside this checked
  coordinate slice, and Cavalieri's integration-to-volume implication remains
  one explicit cite-layer trust. Concrete coordinate instances must be checked
  directly; arbitrary-set `abstract_prop` substitutes are rejected.

### Native complex numbers

- **Ordinary meaning:** Complex arithmetic, real and imaginary coordinates,
  conjugation, and modulus.
- **Semantic role:** Native carrier `C`, native objects `i`, `re`, `img`, and
  `C_abs`, plus `have fn complex_conjugate(z C) C`.
- **Ideal Litex form:** `complex_conjugate(z) = re(z) - img(z) * i`.
- **Nearest wrong alternative:** A custom `struct C` conflicts with the native
  scalar carrier and loses builtin arithmetic facts.
- **Dependencies:** Native complex coordinate reconstruction and extensionality.
- **Downstream uses:** Chapter 8 arithmetic and coordinate examples.
- **Allowable hole:** Ordered comparisons, complex trigonometry, and numeric
  execution remain outside the native symbolic layer.

### Sequences, counting, probability, and statistics

- **Ordinary meaning:** Explicit and recursive sequences, induction, finite
  counts, conditional probability, expectation, variance, regression, and
  descriptive statistics.
- **Semantic role:** Numeric constructions are `have fn`; admissibility and
  statistical judgments are `prop`; major identities are source-facing
  theorems.
- **Ideal Litex form:** `have fn uniform_probability(S finite_set, A power_set(S): ...) R`,
  `prop independent_uniform_events(...)`, a recursive Pascal-entry function,
  formula-defined distribution relations, and `have fn sample_covariance3(...) R`.
- **Nearest wrong alternative:** An arbitrary `choose_fn`, an unparameterized
  `abstract_prop` distribution name, or a theorem declaring arbitrary events
  independent does not model the source mathematics.
- **Dependencies:** Finite sequences and sets, products and sums, factorial,
  square roots, Cauchy--Schwarz, and probability-space laws.
- **Downstream uses:** Chapters 11, 12, 16, 18, 19, and 20.
- **Allowable hole:** The finite binomial coefficient sum still needs checked
  induction/reindexing support, and broad inferential-statistics semantics are
  outside this slice. The recursive combination function, Pascal recurrence,
  Bernoulli/binomial-mass formulas, centered-data Cauchy--Schwarz correlation
  bound, grouped-frequency data, percentile rank, and uniform finite-event
  multiplication are checked directly.

### Derivative relations

- **Ordinary meaning:** Difference quotients, derivatives, derivative
  functions, monotonicity, stationary points, and optimization.
- **Semantic role:** Candidate derivative and monotonicity conditions are
  `prop`; elementary model functions are `have fn`; derivative rules are
  theorems.
- **Ideal Litex form:** `prop has_derivative_at_R(X set, f fn(x R) R, x0, L R)`.
- **Nearest wrong alternative:** An opaque derivative value without existence
  and uniqueness would hide the limit relation required by later analysis.
- **Dependencies:** Real limits, continuity, and the mean-value theorem.
- **Downstream uses:** Chapter 17.
- **Allowable hole:** Derivative-sign monotonicity may remain cited until a
  mean-value theorem is available. Linear and square difference quotients are
  checked directly.

## Dependency map

Edge legend: `signature` means a carrier occurs in an interface; `definition`
means a body uses the dependency; `proof` means a result cites it;
`selection` means unique existence creates a canonical function; `checked-cite`
marks a shared checked theorem; and `trust/source` marks an omitted source or
library proof.

```text
native scalar/set/function carriers
  ->[signature] chapters 1--4
  ->[signature] coordinate vectors (chapters 7, 9, 15)
  ->[signature] finite data (chapters 11, 12, 16, 18--20)
native trigonometry ->[definition/proof] chapters 5, 6, 10, 14
plane dot product (chapter 7) ->[definition] lines and circles (chapter 13)
space dot product (chapter 9) ->[definition] space vectors (chapter 15)
circle unique-center relation ->[selection] center_of_circle (chapter 13)
native complex coordinates ->[definition/proof] complex_conjugate (chapter 8)
HighSchoolCite ->[checked-cite] chapters 1, 4, 11, 12, 18--20
HighSchoolCite ->[trust/source] chapters 4, 9--12, 17, 18
chapters 1--20 ->[proof] eleven direction exercise companions
```

The graph is acyclic. The source order is retained, with the only deliberate
deviations being reuse of the earlier plane and space dot products instead of
redeclaring them, and distinct names for scalar-three and finite-sequence
means to avoid an artificial overload.

## Intended build order

1. Load the shared cite boundary.
2. Build required-1 chapters 1--4.
3. Build required-2 chapters 5--8, using native trigonometry and complex scalars.
4. Build required-3 chapters 9--12.
5. Build optional-1 chapters 13--16, reusing coordinate operations.
6. Build optional-2 chapters 17--20.
7. Run the eleven direction exercise companions against the completed chapter
   namespace surface.

## Interface decisions and permissible gaps

Preserve the native `C` migration, set-valued geometric constructions,
relation-versus-function distinctions, and source-unit chapter boundaries.
Do not restore duplicate `dot2`/`dot3` declarations, conflate the two mean
functions, or turn cited theorem debt into chapter-local assumptions. The
remaining five trusts and one volume interface must remain visible in the
paired workspace todo until replaced by checked mathematics.
