# Mathematical Collections

## Purpose and scope

This module formalizes Terence Tao's *Analysis II*, fourth edition, from the
repository-local transcript `scripts/Analysis2/Analysis II.txt`. The book
continues Analysis I through metric spaces, continuous maps, uniform
convergence, power and Fourier series, several-variable calculus, Lebesgue
measure, and Lebesgue integration.

Standalone exercises are excluded. A named non-exercise result whose proof is
delegated to an exercise remains a source-facing theorem with an explicit
proof-debt boundary until the proof is supplied. The immediate implementation
scope is Chapter 1; later chapters appear below only where their dependency
direction constrains the foundational interfaces.

The intended readers are Litex users learning analysis and contributors using
the translation to discover genuine language, library, inference, kernel, and
diagnostic gaps.

## Modeling conventions

- A metric space is represented by its carrier `X`, its callable distance
  `dist`, and the residual law predicate `$is_metric_space(X, dist)`. The
  distance is not hidden inside a proposition.
- Function domains carry membership information. A sequence in `X` is a
  function `fn(n N_pos) X`; subsets use `power_set(X)`.
- Source constructions that return sets, such as balls, interior, boundary,
  and closure, are `have fn` declarations inside a `template<X, dist>` because
  their domain and codomain depend on the ambient metric space. Pointwise
  membership conditions remain `prop`s.
- A candidate limit is a relation. Convergence is existence of such a
  candidate. A selected metric limit is introduced only after uniqueness.
- The source's arbitrary integer starting index is normalized to `N_pos` in
  the main interface. Chapter 1 explicitly observes that finite changes of
  starting index do not affect convergence, and all later source-facing
  sequence results use positive indices.
- A subsequence is a relation witnessed by a strictly increasing positive
  index map. The displayed subsequence remains an ordinary function value.
- Compactness follows Tao's sequential definition. Open-cover compactness is
  a theorem, not a second definition of compactness.
- `trust` records proof status only. It may defer a proof, selection,
  well-definedness, or source-omitted step without changing the semantic form
  of the underlying object or relation.

The explicit `(X, dist)` presentation is preferred to a `struct` in Chapter 1.
Every source theorem applies the distance directly, while current Litex
function signatures cannot use a struct view object as a function-domain
carrier. Bundling would therefore add projection and retyping work without a
downstream consumer that needs the package as a single value.

## Mathematical spine

### Metric-space laws

- **Ordinary meaning:** A distance on a carrier is nonnegative, separates
  points, is symmetric, and satisfies the triangle inequality.
- **Semantic role:** Structure laws on supplied data.
- **Ideal Litex form:** A callable parameter
  `dist fn(x, y X) R` plus `prop is_metric_space`.
- **Interface sketch:**

  ```litex
  prop is_metric_space(X set, dist fn(x, y X) R):
      forall x, y X:
          dist(x, y) >= 0
          (dist(x, y) = 0 <=> x = y)
      forall x, y X:
          dist(x, y) = dist(y, x)
      forall x, y, z X:
          dist(x, z) <= dist(x, y) + dist(y, z)
  ```

- **Nearest wrong alternative:** A proposition describing an unnamed metric
  value would prevent later code from applying `dist(x,y)`.
- **Dependencies:** `X` and `R` by `signature`; order and arithmetic by
  builtin support.
- **Downstream uses:** Metric convergence, balls, Cauchy sequences, topology,
  compactness, and every later chapter. Probe: derive `dist(x,x)=0` from the
  separation clause.
- **Allowable hole:** Proofs that concrete distances satisfy the laws may be
  deferred individually; the law predicate itself must remain defined.

### Concrete distances

- **Ordinary meaning:** The real, restricted, finite-dimensional
  `l1`/`l2`/`linf`, and discrete distances are callable examples.
- **Semantic role:** Formula-defined functions.
- **Ideal Litex form:** an ordinary `have fn` for the real metric and a
  `template` containing `have fn` for distances whose type depends on a
  carrier.
- **Interface sketch:**

  ```litex
  have fn real_distance(x, y R) R = abs(x - y)
  template<X set, dist fn(x, y X) R, Y power_set(X)>:
      have fn restricted_distance(x, y Y) R = dist(x, y)
  template<X set>:
      have fn discrete_distance(x, y X) R = 0 if x = y else 1
  ```

- **Nearest wrong alternative:** `prop has_distance(x,y,r)` would require an
  extra witness at every use and would not represent the source-defined map.
- **Dependencies:** Metric-space laws by `law`; finite sums, square roots, and
  finite maxima for the coordinate metrics by `definition`.
- **Downstream uses:** Examples 1.1.4--1.1.13, Proposition 1.1.18,
  Proposition 1.1.19, and the Euclidean Heine--Borel theorem.
- **Current implementation:** `l1_distance` is the coordinate absolute-value
  sum. `l2_distance` uses `sqrt(abs(sum of squares))`; the `abs` is a
  well-definedness bridge and is mathematically redundant once nonnegativity
  of the finite sum is proved. `linf_distance` is selected from the unique
  coordinate maximum relation because instantiating the direct recursive
  maximum template currently loses its recursive function binding. This
  selected form is an explicit trusted workaround, not the intended final
  definition.
- **Allowable hole:** The Cauchy--Schwarz proof behind the Euclidean triangle
  inequality and equivalence estimates may remain explicit proof debt. The
  `l2` nonnegativity bridge and the `linf` recursive-template kernel problem
  must remain visible until the direct formulas verify.

### Metric convergence and selected limit

- **Ordinary meaning:** A sequence approaches a displayed point when every
  positive tolerance eventually bounds its distance to that point.
- **Semantic role:** Candidate relation, existence property, uniqueness
  result, then canonical selection.
- **Ideal Litex form:** `prop has_metric_limit`,
  `prop is_metric_convergent`, `thm metric_limit_unique`, and
  `have fn metric_limit ... by exist!`.
- **Interface sketch:**

  ```litex
  prop has_metric_limit(X set, dist fn(x, y X) R, u fn(n N_pos) X, a X):
      forall epsilon R_pos:
          exist N0 N_pos st {
              forall n N_pos:
                  n >= N0
                  =>:
                      dist(u(n), a) <= epsilon
          }
  ```

- **Nearest wrong alternative:** A single predicate called `metric_limit`
  would conflate a candidate relation with the selected value.
- **Dependencies:** Metric laws by `proof`; positive-index sequences by
  `signature`; uniqueness by `proof`; selection by
  `existence/uniqueness/selection`.
- **Downstream uses:** Subsequences, limit points, Cauchy sequences,
  completeness, compactness, and continuity in Chapter 2. Probe:
  `$has_metric_limit(X,dist,u,metric_limit(X,dist,u))`.
- **Current implementation:** Lemma 1.1.1 is checked in both directions for
  `real_distance`: the same epsilon tail works after the formula bridge
  `real_distance_eq_abs` and the explicit normalization
  `abs(abs(t) - 0) = abs(t)`.
- **Allowable hole:** Source-deferred uniqueness may remain trusted, but the
  selected function must be justified by an explicit unique-existence
  boundary rather than an arbitrary choice. The current chapter exposes the
  relation and convergence predicate but not the selected function: generic
  dependent `have fn ... by exist!` rejects the set-valued result, while the
  templated form does not propagate its selection certificate to an immediate
  caller. This is recorded as a `kernel_problem`.

### Metric balls and point-set constructions

- **Ordinary meaning:** A ball collects points within a radius; interior,
  exterior, boundary, and closure collect points satisfying the corresponding
  local ball conditions.
- **Semantic role:** Set-valued functions backed by point relations.
- **Ideal Litex form:** `template<X, dist>` containing `have fn metric_ball`,
  point `prop`s parameterized by the ambient space, and template-contained
  `have fn` declarations for `metric_interior`, `metric_exterior`,
  `metric_boundary`, and `metric_closure`.
- **Interface sketch:**

  ```litex
  template<X set, dist fn(x, y X) R>:
      have fn metric_ball(center X, radius R_pos) power_set(X) =
          {x X: dist(x, center) < radius}
  ```

- **Nearest wrong alternative:** Relations such as
  `is_ball(B,center,radius)` would hide the canonical set used by membership,
  subset, union, and complement expressions. An explicit `X set` argument in
  a non-template `have fn` head also fails to express the dependent return
  type.
- **Dependencies:** Metric laws by `law`; set builders by `definition`.
- **Downstream uses:** Open/closed sets, relative topology, open covers, and
  Chapter 2 continuity. The checked `metric_ball_contains_center` and
  `metric_ball_subset_contains_center` lemmas expose the center-membership
  bridge needed by the point-set proofs. Corollary 1.2.11 is checked as the
  two pointwise closure decompositions. Probe:
  `center $in \metric_ball<X, dist>(center, radius)`.
- **Allowable hole:** Sequential characterization of closure may depend on
  explicit countable choice and can remain a theorem-level proof boundary.

### Open, closed, and relative subsets

- **Ordinary meaning:** Open sets contain a ball around each member; closed
  sets contain every adherent point. Relative openness and closedness apply
  the same notions in a metric subspace.
- **Semantic role:** Relations on candidate subsets.
- **Ideal Litex form:** `prop is_metric_open`,
  `prop is_metric_closed`, `prop is_relatively_metric_open`, and
  `prop is_relatively_metric_closed`.
- **Interface sketch:**

  ```litex
  prop is_metric_open(X set, dist fn(x, y X) R, E power_set(X)):
      forall x E:
          exist radius R_pos st {
              \metric_ball<X, dist>(x, radius) $subset E
          }
  ```

- **Nearest wrong alternative:** A selected topology object is unnecessary
  for Chapter 1 and would make optional Chapter 2.5 vocabulary an upstream
  dependency.
- **Dependencies:** Balls and set complement by `definition`; the checked
  `metric_ball_member_implies_distance_lt` and
  `metric_distance_lt_implies_ball_member` bridges; closure by `proof`.
- **Downstream uses:** Proposition 1.2.15, Proposition 1.3.4, open covers,
  continuity, and connectedness.
- **Current implementation:** The two open/interior and closed/closure
  equivalence directions, the two complement directions (using
  `metric_boundary_of_complement_is_boundary`), the closedness of metric
  singletons and closed balls, the inclusion of every open subset of `E` in
  `metric_interior(E)`, and the inclusion of `metric_closure(E)` in every
  closed superset of `E` are checked directly in Proposition 1.2.15.
- **Allowable hole:** Arbitrary-union and arbitrary-intersection proofs still
  require a stable family-membership or pointwise-to-subset bridge.

### Subsequences and limit points

- **Ordinary meaning:** A subsequence is obtained along a strictly increasing
  positive index map. A limit point is approached arbitrarily far along the
  original sequence.
- **Semantic role:** Relations.
- **Ideal Litex form:** `prop is_strictly_increasing_index`,
  `prop is_subsequence_of`, and `prop is_metric_limit_point`.
- **Interface sketch:**

  ```litex
  prop is_metric_limit_point(
      X set, dist fn(x, y X) R, u fn(n N_pos) X, a X
  ):
      forall N0 N_pos, epsilon R_pos:
          exist n N_pos st {n >= N0, dist(u(n), a) <= epsilon}
  ```

- **Nearest wrong alternative:** A chosen subsequence function would impose a
  noncanonical selection where the source asserts existence.
- **Dependencies:** Positive indices by `signature`; metric convergence by
  `proof`.
- **Downstream uses:** Proposition 1.4.5 and the sequential definition of
  compactness.
- **Current implementation:** `convergent_subsequence_has_same_limit` is
  checked by deriving `phi(n) >= n` with positive-index induction and
  transporting the original convergence tail through the subsequence equation.
  The reverse half of Proposition 1.4.5 similarly turns a late convergent
  subsequence term into a sequence-limit-point witness.
- **Allowable hole:** Constructing a strictly increasing witness from the
  limit-point relation may use countable choice and recursive selection.

### Cauchy sequences and completeness

- **Ordinary meaning:** A sequence is Cauchy when sufficiently late terms are
  mutually close. A metric space is complete when every Cauchy sequence has a
  metric limit in the carrier.
- **Semantic role:** Relations/properties.
- **Ideal Litex form:** `prop is_metric_cauchy` and
  `prop is_complete_metric_space`.
- **Interface sketch:**

  ```litex
  prop is_complete_metric_space(X set, dist fn(x, y X) R):
      forall u fn(n N_pos) X:
          $is_metric_cauchy(X, dist, u)
          =>:
              exist a X st {$has_metric_limit(X, dist, u, a)}
  ```

- **Nearest wrong alternative:** A completion object is not needed for
  Definition 1.4.10 and belongs only to the excluded exercise construction.
- **Dependencies:** Metric convergence and Cauchy relation by `definition`.
- **Downstream uses:** Closed-subspace completeness, compactness, and the
  contraction mapping theorem in Chapter 6.
- **Current implementation:** `metric_convergent_implies_cauchy` is checked
  by using one epsilon/3 tail and the metric triangle inequality.
  `cauchy_with_convergent_subsequence_converges` is also checked: it takes a
  Cauchy tail and a convergent-subsequence tail at epsilon/3, then compares a
  late original term through the corresponding late subsequence term.
- **Allowable hole:** Completeness of `R` is Analysis I background; the two
  closed-subspace transfer directions may remain source-deferred proof debt.

### Compactness and boundedness

- **Ordinary meaning:** Every sequence has a convergent subsequence with its
  limit in the space; a subset is bounded when it lies in some finite-radius
  ball.
- **Semantic role:** Properties of metric spaces and subsets.
- **Ideal Litex form:** `prop is_metric_compact` and
  `prop is_metric_bounded`.
- **Interface sketch:**

  ```litex
  prop is_metric_compact(X set, dist fn(x, y X) R, Y power_set(X)):
      forall u fn(n N_pos) Y:
          exist a Y, phi fn(n N_pos) N_pos st {
              $is_strictly_increasing_index(phi),
              $has_metric_limit(
                  Y,
                  fn(x, y Y) R {dist(x, y)},
                  fn(n N_pos) Y {u(phi(n))},
                  a
              )
          }
  ```

- **Nearest wrong alternative:** Defining compactness by open covers would
  replace Tao's source definition and make Theorem 1.5.8 tautological.
- **Dependencies:** Subsequence and convergence by `definition`; completeness
  and boundedness by `proof`.
- **Downstream uses:** Heine--Borel, open-cover finite subcovers, nested
  compact intersections, and Chapter 2 preservation theorems.
- **Allowable hole:** Finite choice, Euclidean Heine--Borel transport, and the
  open-cover proof may remain theorem-level debt while the sequential
  definition stays concrete.

### Open covers and family operations

- **Ordinary meaning:** A family of open subsets covers a set when every point
  lies in one member; a finite subcover is a finite subfamily with the same
  property.
- **Semantic role:** Set-valued construction and relations.
- **Ideal Litex form:** `have fn family_union`, `prop is_metric_open_cover`,
  and `prop has_finite_subcover`.
- **Interface sketch:**

  ```litex
  prop is_metric_open_cover(
      X set, dist fn(x, y X) R,
      Y power_set(X), cover power_set(power_set(X))
  ):
      forall V cover:
          $is_metric_open(X, dist, V)
      Y $subset family_union(X, cover)
  ```

- **Nearest wrong alternative:** Hiding the cover inside a trusted compactness
  predicate would erase the source theorem and its finite witness.
- **Dependencies:** Open sets and set-family union by `definition`; finite
  sets by `signature`.
- **Downstream uses:** Theorem 1.5.8 and Corollary 1.5.9.
- **Allowable hole:** Theorem 1.5.8's radius infimum and recursive separated
  sequence construction may remain a visible substantial proof boundary.

### Later-book spines

Continuous maps consume metric balls and metric limits. Uniform convergence
consumes metric/real limits and function spaces. Power and Fourier series
consume uniform convergence, finite sums, and selected limits. Several-variable
calculus consumes metric continuity and typed linear maps. Lebesgue measure
requires a callable extended-nonnegative set function and a measurable-set
relation; Lebesgue integration then builds simple, nonnegative, and absolutely
integrable layers. These later concepts must not force Chapter 1 to publish
speculative wrappers.

## Dependency map

Edge legend: `signature`, `definition`, `law`, `well_definedness`,
`existence`, `uniqueness`, `selection`, `proof`, `import`, and
`trust/source`.

```text
X + dist --signature/law--> is_metric_space
is_metric_space --law--> real/restricted/discrete/coordinate examples

positive-index sequence + is_metric_space
  --definition--> has_metric_limit
has_metric_limit --definition--> is_metric_convergent
has_metric_limit --proof/uniqueness--> metric_limit_unique
is_metric_convergent + metric_limit_unique
  --existence/uniqueness/selection--> metric_limit

is_metric_space --definition--> metric_ball
metric_ball --definition--> interior/exterior/boundary/adherent
adherent --definition--> metric_closure
interior/adherent --definition--> open/closed
open/closed + restricted_distance
  --definition--> relative open/closed

strictly increasing index --definition--> subsequence relation
has_metric_limit + subsequence relation
  --proof--> subsequence limit preservation
limit-point relation
  --proof/existence--> convergent subsequence

is_metric_space --definition--> is_metric_cauchy
has_metric_limit --proof--> convergent implies Cauchy
is_metric_cauchy + convergent subsequence
  --proof--> Cauchy sequence converges
is_metric_cauchy + has_metric_limit
  --definition--> complete metric space
complete + closed
  --proof--> closed-subspace completeness equivalence

subsequence relation + has_metric_limit
  --definition--> compactness
compactness --proof--> completeness and boundedness
compactness + relative closedness --proof--> compact subsets are closed
compactness + open cover
  --proof--> finite subcover
finite subcover --proof--> nested compact intersection
```

There is no intended cycle. The selected metric limit follows the uniqueness
result even though the source introduces limit notation immediately after
Proposition 1.1.20. Compactness remains sequential; the open-cover theorem is
downstream.

## Intended build order

1. Metric laws and concrete distance functions.
2. Candidate metric limit, convergence, uniqueness, and selected limit.
3. Balls and the interior/exterior/boundary/closure set constructors.
4. Open/closed sets and relative topology.
5. Subsequence indices, subsequence relation, and limit points.
6. Cauchy sequences, completeness, and closed-subspace transfer.
7. Compactness, boundedness, Euclidean Heine--Borel, open covers, nested
   intersections, and finite compact unions.
8. Chapter 2 continuity only after the Chapter 1 interfaces and use probes
   verify in the ordered project.

## Interface decisions and permissible gaps

- Preserve the explicit carrier and callable distance in every public
  interface; do not replace them with a proposition-only metric object.
- Keep candidate limits, convergence, and selected limits separate.
- Keep set-valued topology constructions callable.
- Use `N_pos` as the canonical sequence index for this module and record the
  source's arbitrary-start convention in comments.
- Keep compactness sequential and prove open-cover compactness as a theorem.
- Source-deferred proofs may be trusted only at the exact result or substep
  the source omits. Full source proofs that remain blocked require an exact
  working note and smallest identified missing interface.
