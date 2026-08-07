# Mathematical Collections

## Purpose and scope

This module formalizes Terence Tao's *Analysis II*, fourth edition, from the
repository-local transcript `scripts/Analysis2/Analysis II.txt`. The book
continues Analysis I through metric spaces, continuous maps, uniform
convergence, power and Fourier series, several-variable calculus, Lebesgue
measure, and Lebesgue integration.

Standalone exercises are excluded. A named non-exercise result whose proof is
delegated to an exercise remains a source-facing theorem with an explicit
proof-debt boundary until the proof is supplied. Chapter 1 is implemented and
Chapter 2 is the active implementation scope; later chapters appear below only
where their dependency direction constrains the foundational interfaces.

The intended readers are Litex users learning analysis and contributors using
the translation to discover genuine language, library, inference, kernel, and
diagnostic gaps.

## Modeling conventions

- A metric space is represented by its carrier `X`, its callable distance
  `dist`, and the residual law predicate `$is_metric_space(X, dist)`. The
  distance is not hidden inside a proposition.
- Function domains carry membership information. A sequence in `X` is a
  function `fn(n N+) X`; subsets use `power_set(X)`.
- Source constructions that return sets, such as balls, interior, boundary,
  and closure, are `have fn` declarations inside a `template<X, dist>` because
  their domain and codomain depend on the ambient metric space. Pointwise
  membership conditions remain `prop`s.
- A candidate limit is a relation. Convergence is existence of such a
  candidate. A selected metric limit is introduced only after uniqueness.
- The source's arbitrary integer starting index is normalized to `N+` in
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
- **Source-example result layer:** Examples 1.1.4 and 1.1.5 must explicitly
  certify `real_distance` and every restricted metric as metric spaces;
  defining their formulas alone does not establish the examples. Examples
  1.1.6, 1.1.7, and 1.1.9 must likewise certify the finite-dimensional
  `l2`, `l1`, and `linf` functions and retain the displayed two-dimensional
  values and comparison inequalities. Example 1.1.11 certifies the selected
  discrete distance on every carrier. These are named theorem results over
  the concrete callable functions, not new distance predicates or arbitrary
  caller-supplied metrics. Their metric-law proofs are source-deferred
  `proof/trust-source` edges, while simple displayed evaluations should be
  checked directly whenever current normalization supports them.
- **Binary mismatch layer:** Remark 1.1.8 should not be represented only as
  prose about coding theory. For two finite binary vectors, the important
  reusable object is the finite set of coordinate indices on which they
  differ; the remark's mathematical claim is that `l1_distance` equals the
  size of this set. The displayed strings `10010` and `10101` should then
  instantiate that interface and return distance `3`. This is a
  template-contained finite-set construction plus named theorem results, not
  a new metric or a string-encoding subsystem.
- **Metric-sensitive sequence example:** Example 1.1.17 should bind one
  concrete plane-valued sequence with both coordinates `1/n` and one concrete
  origin with zero coordinates, then state all four source outcomes over
  `l2_distance`, `l1_distance`, `linf_distance_for_dimension`, and
  `discrete_distance`. It is a worked use of existing metric-limit
  interfaces, not a new convergence predicate or four unrelated sequences.
- **Convergence compatibility layer:** Remark 1.1.15 should connect
  `has_metric_limit(R, real_distance, u, a)` to the ordinary absolute-value
  epsilon-tail relation, making the claimed generalization explicit rather
  than relying on prose or notation. Remark 1.1.16 should expose the only
  mathematically substantive invariance in that remark: requiring the tail
  witness to lie after any fixed positive starting index is equivalent to the
  unrestricted metric-limit predicate. Dummy-variable renaming remains
  alpha-equivalence and needs no separate theorem.
- **Ambient/subspace worked-set layer:** Examples 1.3.1 and 1.3.2 require
  distinct typed presentations of the same point conditions. The open
  x-axis segment needs an ambient `power_set(finite_real_vector<2>)` version
  and a `power_set(x_axis)` version; `[0,1)` likewise needs an ambient real
  version and a version over the carrier `(-1,1)`. The result layer should
  state both ambient failure and relative success, plus the displayed origin
  ball/adherence facts that explain the difference. Do not collapse these
  into one untyped set or into the generic relative-topology proposition.
- **Open/closed classification examples:** Example 1.2.13 should expose the
  exact boundary `{1,2}` for `(1,2)`, `[1,2]`, and `[1,2)`, together with the
  resulting open, closed, or neither classification. Remark 1.2.14 should
  package the empty boundaries and clopen status of the whole carrier and
  empty set, then state that every subset is clopen under the discrete
  metric. These result packages consume the existing boundary-based
  definitions; they are not alternate definitions of open and closed.
- **Subsequence and incompleteness worked layer:** Example 1.4.2 should bind
  the displayed plane sequence and its square-index subsequence, plus the
  alternating zero-one sequence and its constant-one odd-index subsequence.
  Example 1.4.8 should expose a rational-valued Cauchy sequence that converges
  to `pi` after embedding in `R` but has no rational limit. Until decimal
  truncation or floor support exists, keep the specific
  `3,3.1,3.14,...` construction as visible proof debt rather than inventing a
  different formula. Example 1.4.11 should consume this distinction to state
  completeness of `R` and incompleteness of `Q`.
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
  prop has_metric_limit(X set, dist fn(x, y X) R, u fn(n N+) X, a X):
      forall epsilon R+:
          exist N0 N+ st {
              forall n N+:
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
      have fn metric_ball(center X, radius R+) power_set(X) =
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
- **Concrete probes:** Examples 1.2.2 and 1.2.3 should retain their actual
  balls rather than merely restating the generic definition. The planar
  origin, Euclidean unit disc, taxicab unit diamond, discrete singleton, and
  real interval `(3,7)` are named set data; the results identify each with
  the corresponding canonical `metric_ball`. The discrete example also
  exposes that every radius greater than one gives the whole carrier. The
  nearest rejected form is an arbitrary supplied set assumed equal to a ball,
  or detached coordinate inequalities with no equality to `metric_ball`.
  These probes depend on the concrete `l1`, `l2`, real, and discrete metrics
  by `definition`; square-root/absolute-value normalization in the Euclidean
  equality may remain a localized `trust/source` proof edge.
  Examples 1.2.7 and 1.2.8 should then exercise the derived point-set
  constructors rather than introduce parallel predicates. For `[1,2)`, the
  source-facing result binds the interior point `1.5`, exterior point `3`,
  boundary points `1,2`, and the exact interior, exterior, and boundary sets,
  including the fact that one boundary endpoint belongs to the set and the
  other does not. For an arbitrary subset under the discrete metric, the
  interior is the subset, the exterior is its complement in the carrier, and
  the boundary is empty. The nearest rejected form is a list of detached
  point facts with no equality to `metric_interior`, `metric_exterior`, and
  `metric_boundary`. These examples depend on the canonical constructors by
  `definition`; their uniform ball calculations may remain localized
  `trust/source` edges.

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
          exist radius R+ st {
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
      X set, dist fn(x, y X) R, u fn(n N+) X, a X
  ):
      forall N0 N+, epsilon R+:
          exist n N+ st {n >= N0, dist(u(n), a) <= epsilon}
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
      forall u fn(n N+) X:
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
      forall u fn(n N+) Y:
          exist a Y, phi fn(n N+) N+ st {
              $is_strictly_increasing_index(phi),
              $has_metric_limit(
                  Y,
                  fn(x, y Y) R {dist(x, y)},
                  fn(n N+) Y {u(phi(n))},
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

### Metric continuity at a point and on a space

- **Ordinary meaning:** A map is continuous at `a` when every positive output
  tolerance admits a positive input tolerance that controls every nearby
  point. It is continuous on its domain when this holds at every point.
- **Semantic role:** Properties of a supplied typed function. The
  epsilon--delta residual for one chosen pair of tolerances is a reusable
  supporting relation, not a new mathematical object.
- **Ideal Litex form:** `prop is_metric_delta_controlled_at`,
  `prop is_metric_continuous_at`, and `prop is_metric_continuous`, with the
  map retained as an ordinary callable parameter. The source's inverse image
  is a canonical set-valued construction, so it is a template-contained
  `have function_preimage power_set(X)` rather than a relation describing a
  candidate set.
- **Interface sketch:**

  ```litex
  prop is_metric_delta_controlled_at(
      X, Y set,
      dist_X fn(x, y X) R, dist_Y fn(x, y Y) R,
      f fn(x X) Y, a X, epsilon R+, delta R+
  ):
      forall x X:
          dist_X(x, a) < delta
          =>:
              dist_Y(f(x), f(a)) < epsilon

  prop is_metric_continuous_at(
      X, Y set,
      dist_X fn(x, y X) R, dist_Y fn(x, y Y) R,
      f fn(x X) Y, a X
  ):
      forall epsilon R+:
          exist delta R+ st {
              $is_metric_delta_controlled_at(
                  X, Y, dist_X, dist_Y, f, a, epsilon, delta
              )
          }
  ```

- **Nearest wrong alternative:** A `have fn` called continuity would pretend
  that continuity returns a value; a bundled continuity object would hide the
  function that later composition, image, and arithmetic theorems must apply.
- **Dependencies:** Typed carriers and callable maps by `signature`; both
  metric functions by `signature`; Chapter 1 metric laws, limits, open sets,
  and closed sets by later `proof`.
- **Downstream uses:** Sequential and open-set characterizations, composition,
  product-space continuity, compact images, uniform continuity, connected
  images, and every later preservation theorem. Immediate probes are
  unfolding domain continuity at a chosen point, checking inverse-image
  membership directly from its set builder, and composing two epsilon--delta
  witnesses.
- **Allowable hole:** The source assigns the sequential and open/closed
  characterization proofs to exercises, so those theorem bodies may initially
  carry narrow `trust` boundaries. The predicates themselves must be concrete,
  and composition remains an explicit proof target.

### Pairing and real arithmetic maps

- **Ordinary meaning:** Two real-valued functions on the same domain combine
  pointwise into an `R^2`-valued function. Addition, subtraction,
  multiplication, maximum, minimum, division away from zero, and scalar
  multiplication are ordinary callable maps used by composition.
- **Semantic role:** Formula-defined functions, followed by continuity
  theorems about those functions.
- **Ideal Litex form:** A template-contained `have fn real_function_pair`
  returning `\chap1::finite_real_vector<2>`, plus ordinary `have fn`
  declarations for the arithmetic maps. Continuity remains expressed with the
  existing metric continuity predicates.
- **Interface sketch:**

  ```litex
  have fn real_pair_coordinate(a, b R, j closed_range(1, 2)) R by cases:
      case j = 1: a
      case j != 1: b

  template<X set, f, g fn(x X) R>:
      have fn real_function_pair(x X) \chap1::finite_real_vector<2> =
          fn(j N+: j <= 2) R {
              real_pair_coordinate(f(x), g(x), j)
          }
  ```

- **Nearest wrong alternative:** A proposition asserting that some vector is
  the pair would hide the callable function needed by composition. A new
  product-space carrier would duplicate Chapter 1's finite real vectors.
- **Dependencies:** `finite_real_vector<2>` and `l2_distance<2>` by
  `signature`; Proposition 1.1.18 and Theorem 2.1.4 by `proof`; real
  arithmetic and finite maximum/minimum formulas by `definition`.
- **Downstream uses:** Lemmas 2.2.1--2.2.2, Corollary 2.2.3, polynomial
  examples, and later multivariable functions.
- **Allowable hole:** Tao assigns both lemmas to exercises. Their theorem
  bodies may initially be trusted, but the paired and arithmetic functions
  must remain concrete and immediately evaluable.

### Images, extrema, and uniform continuity

- **Ordinary meaning:** The image of a subset contains exactly the values
  attained there. A real function is bounded when one absolute bound controls
  every value, and it attains an extremum at a displayed domain point.
  Uniform continuity chooses one input tolerance that works simultaneously
  for every pair of domain points.
- **Semantic role:** The image is a canonical set-valued construction.
  Boundedness, attainment, and uniform continuity are properties of supplied
  functions; a chosen epsilon--delta pair is a residual relation.
- **Ideal Litex form:** `function_image` as a template-contained `have`,
  `is_bounded_real_function`, `attains_real_maximum_at`,
  `attains_real_minimum_at`, `is_uniform_delta_controlled`, and
  `is_metric_uniformly_continuous` as concrete `prop`s.
- **Nearest wrong alternative:** Encoding the image only as an existential
  relation would prevent it from being passed to Chapter 1 compactness.
  Selecting maximum or minimum values before the nonempty compact theorem
  would introduce unnecessary choice.
- **Dependencies:** Function application and subsets by `signature`; Chapter
  1 sequential compactness by `proof`; real distance and order by `proof`;
  ordinary metric continuity by `proof`.
- **Downstream uses:** Theorem 2.3.1, Proposition 2.3.2, Theorem 2.3.5, later
  uniform convergence results, and the contraction mapping theorem.
- **Allowable hole:** The compact-image and maximum-principle proofs are
  exercise-deferred. The compact-to-uniform direction may retain the explicit
  finite-open-cover proof boundary, but uniform-to-pointwise continuity
  should be checked directly from the definitions.

### Connected metric spaces and subsets

- **Ordinary meaning:** A disconnected nonempty metric space splits into two
  disjoint nonempty open subsets that cover the carrier. A connected space is
  nonempty and has no such separation; connected subsets use the restricted
  metric.
- **Semantic role:** Properties of supplied metric data and candidate
  subsets. A displayed pair of separating open sets is a residual witness
  relation.
- **Ideal Litex form:** `is_metric_separation_witness`,
  `is_metric_disconnected`, `is_metric_connected`, and restricted-metric
  subset versions as concrete `prop`s.
- **Nearest wrong alternative:** A selected connected component or topology
  object is not part of the source definition. Omitting nonemptiness would
  incorrectly make the empty set connected, contrary to Tao's convention.
- **Dependencies:** Chapter 1 metric openness and restricted distances by
  `definition`; interval order and supremum reasoning by `proof`; function
  images and open inverse images by `proof`.
- **Downstream uses:** The real-line interval characterization, preservation
  under continuous maps, the intermediate value theorem, and later
  path-connected and component exercises.
- **Allowable hole:** The real-line theorem contains a substantial supremum
  argument, and the preservation/IVT proofs are exercise-deferred. Their
  source-facing conclusions may remain explicit theorem-level debt.
- **Concrete probe:** Example 2.4.2 should expose the actual subset
  `[1,2] union [3,4]` as named data and conclude disconnectedness under the
  restricted usual real metric. An arbitrary supplied disconnected set, or a
  theorem assuming its own separation, would lose the example. The interval
  openness calculation inside the union may remain one localized
  `trust/source` edge.

### Optional topological layer

- **Ordinary meaning:** A topology is a collection of subsets containing the
  empty set and carrier and closed under finite intersections and arbitrary
  unions. Neighborhoods, convergence, interior, exterior, boundary, closure,
  relative topology, continuity, compactness, and connectedness are then
  defined from that supplied collection of open sets.
- **Semantic role:** A topology and relative topology are set-valued data.
  Neighborhood, point, continuity, cover, compactness, and connectedness
  notions are concrete properties. Closure is the canonical set of adherent
  points.
- **Ideal Litex form:** `is_topology_on` and the derived notions as `prop`s;
  `topological_closure` and `relative_topology` as template-contained `have`
  functions. Finite and arbitrary open families use Chapter 1's existing
  set-family intersection and union constructions.
- **Nearest wrong alternative:** Treating a topology as a proposition without
  retaining its open-set collection would make neighborhoods and relative
  topology unusable. Importing a second topology interface from the derived
  corpus would also obscure this textbook's source-local dependency surface.
- **Dependencies:** Chapter 1 set-family union/intersection by `definition`;
  finite sets and function families by `signature`; metric-free set
  membership, intersection, complement, and image reasoning by `definition`.
- **Downstream uses:** The optional reformulation of convergence and
  continuity, topological compactness, connectedness, and later general
  topological examples.
- **Allowable hole:** These are definitions, so their public shapes must be
  concrete and checked. The source leaves proofs that relative collections
  satisfy the topology laws and equivalences with metric notions as exercises;
  those exercises are outside the Chapter 2 named-item inventory.
- **Concrete probe:** Example 2.5.3 needs an explicit relation connecting a
  supplied topology `T` with the metric-open subsets of `(X,dist)`. Given that
  relation, the already defined metric ball must be returned as a
  neighborhood of its center. Merely asserting neighborhood membership
  without connecting `T` to metric openness would make the example
  tautological. The bridge depends on Chapter 1's open-ball theorem by
  `proof/import`.

### Function limits and modes of convergence

- **Ordinary meaning:** A function on a subset has limiting value `L` at an
  adherent ambient point when all sufficiently close domain values map
  epsilon-close to `L`. A sequence of functions converges pointwise when the
  tail index may depend on the argument, and uniformly when one tail index
  works for every argument.
- **Semantic role:** Candidate limiting values, pointwise convergence, and
  uniform convergence are relations on supplied functions. The epsilon-tail
  conditions are residual witness relations.
- **Ideal Litex form:** `has_function_limit`,
  `is_pointwise_convergent_to`, and `is_uniformly_convergent_to` as concrete
  `prop`s over `N+`-indexed function families.
- **Nearest wrong alternative:** A selected function-limit value would require
  existence and uniqueness not present in the definition. Encoding a function
  family as an untyped set would lose callable applications `family(n)(x)`.
- **Dependencies:** Chapter 1 metric limits/adherence by `definition`; Chapter
  2 metric continuity by `proof`; positive-index sequences and typed functions
  by `signature`.
- **Downstream uses:** Sequential and neighborhood characterizations,
  preservation of continuity and boundedness, uniform metrics, function
  series, and interchange theorems.
- **Allowable hole:** Exercise-deferred characterization and preservation
  theorems may retain theorem-level trust, but all convergence relations must
  be concrete and useable.

### Bounded-function spaces and the uniform metric

- **Ordinary meaning:** `B(X -> Y)` contains exactly the bounded maps from `X`
  to `Y`; the uniform distance is the supremum of pointwise distances, with
  value zero on an empty domain. `C(X -> Y)` is its bounded continuous
  subspace.
- **Semantic role:** Function spaces are canonical set-valued constructions.
  Uniform distance is a function on pairs of bounded maps selected from a
  supremum; boundedness and continuity are properties.
- **Ideal Litex form:** `bounded_function_space` and
  `bounded_continuous_function_space` as template-contained `have` sets;
  ultimately `uniform_distance` should be a callable selection. The current
  verified interface is the concrete `is_uniform_distance_value` relation,
  a trusted unique-existence theorem on nonempty domains, and the explicit
  empty-domain value, because generic `have fn ... by exist!` inferred the
  wrong result sort in the real caller context.
- **Nearest wrong alternative:** A predicate alone would not provide the
  carrier needed by Chapter 1 metric completeness. An arbitrary bound is not
  the uniform distance because later convergence needs the least upper bound.
- **Dependencies:** Chapter 2 bounded-function and continuity predicates by
  `definition`; real completeness/supremum by `existence`, `uniqueness`, and
  `selection`; Chapter 1 metric-space/completeness interfaces by `proof`.
- **Downstream uses:** Proposition 3.4.4, Theorem 3.4.5, the sup norm,
  Weierstrass M-test, and all later uniform estimates.
- **Allowable hole:** Selection of the pointwise-distance supremum may remain a
  narrowly trusted construction until a reusable real-supremum interface is
  available. Metric laws and completeness are exercise-deferred theorem debt.

### Function series and the sup norm

- **Ordinary meaning:** The `N`th partial sum is the pointwise finite sum of
  the first `N` functions. A function series converges pointwise or uniformly
  when its partial-sum sequence does. The sup norm is the uniform distance to
  zero.
- **Semantic role:** Partial sum is callable and series convergence is a
  relation. Sup norm is currently a concrete candidate-value relation plus
  the empty-domain value; a callable selection remains downstream of the
  uniform-distance selection gap.
- **Ideal Litex form:** `function_partial_sum` as a template-contained
  `have fn`, pointwise/uniform series convergence as `prop`s, and eventually
  `sup_norm` as a function defined through `uniform_distance`. Chapter 3
  presently publishes `is_sup_norm_value` without pretending the blocked
  selector exists.
- **Nearest wrong alternative:** Merely asserting that a proposed function is
  a partial sum would prevent later code from forming the sequence of partial
  sums. Keeping the norm only as a bound relation would hide the real number
  used by the M-test.
- **Dependencies:** Builtin finite `sum` by `definition`; pointwise and uniform
  convergence by `definition`; bounded-function uniform distance by
  `definition`.
- **Downstream uses:** Definition 3.5.2, Theorem 3.5.7, termwise integration,
  and termwise differentiation.
- **Allowable hole:** The M-test proof is exercise-deferred and depends on the
  trusted completeness theorem for continuous bounded function space.

### Integration and differentiation consumers

- **Ordinary meaning:** Uniform limits commute with Riemann integration on a
  compact interval. Uniform convergence of continuous derivatives, together
  with convergence at one point, produces a differentiable uniform limit.
- **Semantic role:** Riemann-integrability, candidate integral values, and
  derivative-function relations are background properties of supplied
  functions. Chapter 3 results quantify their values/functions explicitly
  rather than inventing an unsupported global selection.
- **Ideal Litex form:** Concrete chapter-local relations
  `has_riemann_integral_on` and `is_derivative_function_on`; theorem statements
  carry integral-value sequences or derivative functions as typed parameters.
- **Nearest wrong alternative:** A trusted global `integral(f)` or
  `derivative(f)` function would conceal existence, uniqueness, and domain
  restrictions. Weakening the source theorem to omit the resulting integral
  or derivative identity would lose its mathematical content.
- **Dependencies:** Closed real intervals by `signature`; Analysis I Riemann
  integration and differentiation theory by `trust/source`; uniform
  convergence and continuity preservation by `proof`.
- **Downstream uses:** Theorems 3.6.1 and 3.7.1 and their series corollaries.
- **Allowable hole:** The background relations are explicit, while the
  substantial source proofs and future-book fundamental-theorem facts may
  remain narrow trusted conclusions.

### Polynomials, support, convolution, and approximation

- **Ordinary meaning:** A polynomial function on an interval has a finite
  coefficient formula. Compact support means vanishing outside some bounded
  interval. Convolution integrates `f(y)g(x-y)`, and approximations to the
  identity are normalized nonnegative compactly supported kernels small away
  from zero.
- **Semantic role:** Polynomialhood, support, and approximation-to-identity
  are properties. Extension by zero and convolution are mathematically
  callable constructions, but the verified current surface keeps both as
  concrete graph relations because dependent piecewise construction and
  integral-value selection are not yet stable.
- **Ideal Litex form:** `is_polynomial_on`, `is_supported_on`,
  `is_compactly_supported`, and `is_approximation_to_identity` as concrete
  `prop`s. The implemented `is_zero_extension` and
  `is_convolution_function` relations are the honest current interfaces;
  callable `zero_extension` and `convolution` should replace them only after
  their construction and uniqueness certificates verify.
- **Nearest wrong alternative:** An opaque `abstract_prop` for convolution or
  a trusted callable function without a construction certificate would hide
  its defining integral. The current graph relation remains usable in the
  algebraic and approximation statements while keeping the gap visible.
  Treating polynomial coefficients as one fixed-length vector would exclude
  arbitrary finite degrees.
- **Dependencies:** Finite sums and real powers by `definition`; Chapter 3
  integration relation by `definition`; compactness/uniform continuity by
  `proof`; integral uniqueness by `uniqueness` and convolution selection.
- **Downstream uses:** Lemmas 3.8.5, 3.8.8, 3.8.13--3.8.16, Corollaries
  3.8.15/18/19, and the full Weierstrass approximation theorem.
- **Allowable hole:** Integral existence/uniqueness for convolution and the
  exercise-deferred approximation lemmas may remain visible trust boundaries.
  The polynomial/support predicates and zero-extension graph must remain
  concrete.

### Formal power series, radius, and analyticity

- **Ordinary meaning:** A formal power series is determined by a center and a
  sequence of coefficients. Its partial sums are callable polynomial
  functions. The radius of convergence may be zero, a finite nonnegative real,
  or positive infinity. A function is analytic at a point when one such series
  agrees with it on a neighborhood.
- **Semantic role:** Coefficients and centers are supplied data;
  `power_series_term` and `power_series_partial_sum` are callable functions;
  convergence, radius, and analyticity are relations. A selected sum function
  is justified only after pointwise unique existence.
- **Ideal Litex form:** `power_series_term` and
  `power_series_partial_sum` as `have fn`; a tagged
  `power_series_radius_value` carrier separating finite radii from infinity;
  a concrete nonnegative coefficient-root sequence, a tagged limsup relation,
  and `is_radius_of_convergence` as the reciprocal Cauchy--Hadamard relation;
  and
  `is_real_analytic_at`/`is_real_analytic_on` as concrete `prop`s.
- **Nearest wrong alternative:** Encoding every radius as a real silently
  discards infinite radius. Treating a formal power series as a proposition
  prevents later chapters from evaluating terms or partial sums. Making
  analyticity an opaque assumption hides its neighborhood and coefficient
  witnesses. Defining the radius by convergence inside and divergence outside
  imports Theorem 4.1.6(a)(b) into Definition 4.1.3 and makes the theorem
  circular.
- **Dependencies:** Natural-index finite sums and real powers by
  `definition`; extended limsup and the infinity convention by
  `trust/source`; Chapter 3 pointwise/uniform series convergence by
  `definition`; differentiation and integration by `trust/source`.
- **Downstream uses:** The radius theorem, analytic derivatives, Taylor
  coefficients, Abel boundary continuity, multiplication, exponential,
  logarithm, and trigonometric series.
- **Allowable hole:** The major exercise-deferred
  convergence/differentiation proofs may remain explicit trust boundaries.
  The coefficient-root, tagged limsup, reciprocal-radius, partial-sum, and
  analytic-witness relations must be concrete.
- **Current implementation:** `formal_power_series_data`,
  `power_series_term`, `power_series_partial_sum`, the tagged
  `power_series_radius`, coefficient-root sequence, finite/infinite limsup,
  reciprocal-radius relation, convergence relations, and analyticity
  predicates are concrete. Theorem 4.1.6(d) concludes a displayed derivative
  function from the power-series hypotheses, identifies it pointwise with the
  termwise derivative series, and records uniform convergence of that series
  on every smaller closed interval. It does not assume differentiability as a
  premise. Part (e) similarly concludes a Riemann integral value and the exact
  integrated coefficient series on every closed interval inside the radius;
  it does not assume the integral value. Theorem 4.1.6 proof conclusions
  remain explicit boundaries.

### Iterated derivatives and Taylor data

- **Ordinary meaning:** The zeroth derivative is the original function and the
  `(k+1)`st derivative is the derivative of the `k`th. Analyticity supplies
  every derivative and identifies each coefficient with the derivative value
  divided by a factorial.
- **Semantic role:** A derivative tower is callable family data with a law
  relation; `is_k_times_differentiable` and `is_smooth` are properties.
- **Ideal Litex form:** derivative relations may consume a supplied tower, but
  an existence theorem such as Proposition 4.2.6 must construct one callable
  family `derivatives fn(k N) fn(x E) R` together with its coefficient family.
  Constrain the zeroth member and every successive derivative step, and state
  the power-series and Taylor identities against that same witness. Do not
  introduce a global derivative selector before the Analysis I derivative API
  is available.
- **Nearest wrong alternative:** A recursive proposition that cannot expose
  `f^(k)(x)` is unusable in Taylor's formula. Conversely, universally
  quantifying arbitrary derivative and coefficient families in Proposition
  4.2.6 turns the intended existence conclusion into a false requirement on
  caller-supplied data. A trusted global derivative function would conceal
  existence and domain conditions.
- **Dependencies:** Chapter 3's explicit derivative relation by
  `trust/source`; factorial and finite products by `definition`; analytic
  power-series witnesses by `definition`.
- **Downstream uses:** Propositions 4.2.6, Corollaries 4.2.7/10/12, and the
  exponential and trigonometric derivative identities.
- **Allowable hole:** Successive differentiation laws remain trusted until
  the concrete Analysis I API is connected.
- **Current implementation:** `is_derivative_tower`,
  `is_k_times_differentiable`, recursive `factorial_real`, and the
  multiplication-based derivative-coefficient relation are concrete.
  Proposition 4.2.6 returns one derivative family and one coefficient family
  that satisfy every finite tower, the factorial relation, and every local
  power-series expansion. Corollary 4.2.7 likewise returns one global family
  whose zeroth member is the source function, whose finite prefixes are
  derivative towers, and whose members are analytic. Taylor's formula returns
  local derivative data on the actual expansion interval and attaches
  `f^(k)(a)=k!c_k` to that same witness. None of these results places
  derivative conclusions on an arbitrary supplied family. The local
  construction, global patching, and Taylor derivation remain trusted.
  Power-series uniqueness keeps the source domain `E` visible: both positive
  expansion intervals lie inside `E` and refer to the same `f:E -> R`.
  Abel's endpoint theorems retain the finite tagged radius relation instead of
  treating an arbitrary interval half-width as the named convergence radius.
  General real series use `has_zero_indexed_series_sum`; the name does not
  falsely imply that the summands are nonnegative.
  The product theorem consumes analytic functions with expansions on the
  whole interval and returns both product analyticity and the convolution
  expansion there. Mere convergence of two series at one point is not enough
  for the Cauchy-product conclusion.
  The exponential theorem keeps every source clause visible: infinite radius,
  pointwise absolute convergence and the selected series value, analyticity,
  derivative, continuity and integral, addition, normalization, positivity,
  reciprocal, and both order directions.
  The logarithm theorem likewise records both forms of its series clause: the
  `ln(1-x)` series and the Taylor expansion centered at one, including radius
  one and analyticity at the center.
  Complex arithmetic law packages retain both distributive directions,
  conjugation's equality/fixed-point equivalences, both directions of the
  zero-modulus criterion, and the sum, difference, scalar-product, product,
  conjugate, and quotient limit laws.
  The trigonometric layer keeps both Euler formulas and the defining
  consequences `sin(pi)=0`, `cos(pi)=-1`, and `exp(pi i)=-1` visible.

### Exponential, logarithm, and complex arithmetic

- **Ordinary meaning:** The real exponential is the sum of its everywhere
  convergent power series; logarithm is its inverse. Complex numbers are real
  coordinate pairs with coordinatewise addition, the standard complex
  product, conjugation, modulus, reciprocal, and Euclidean metric.
- **Semantic role:** Every operation is callable data. Algebraic, metric, and
  limit laws are propositions or named theorems. Exponential/logarithm values
  require selected unique sums/inverses.
- **Ideal Litex form:** use a two-real-coordinate `ComplexNumber` structure
  (semantically `cart(R,R)`) as the concrete complex carrier; define
  coordinate projections, addition, negation, multiplication,
  conjugation, modulus, reciprocal, and distance by `have fn`. Define real
  exponential and logarithm through explicit candidate relations plus unique
  selection where the verifier supports it.
- **Nearest wrong alternative:** An `abstract_prop` standing for a complex
  number or operation destroys the field-like API. Reusing real arithmetic
  notation without coordinate definitions makes the identification invisible.
- **Dependencies:** Pair projections and real arithmetic by `definition`;
  square root and metric results by `definition/proof`; power-series
  convergence and inverse existence by `trust/source`.
- **Downstream uses:** Sections 4.5--4.7, Euler's formula, sine/cosine, and
  periodicity.
- **Allowable hole:** Unique infinite-series selection and inverse existence
  may remain visible trusted constructions; coordinate operations and their
  source-facing laws must remain explicit.
- **Current implementation:** `exp_real`, `log_real`, and their candidate
  relations are selected interfaces. `ComplexNumber` has concrete
  `real_part` and `im` fields and concrete addition, negation, multiplication, conjugation,
  modulus, reciprocal/quotient, distance, powers, and exponential
  constructions. Algebraic, metric, and limit laws remain trusted.

### Trigonometric functions and pi

- **Ordinary meaning:** Sine and cosine are defined from the complex
  exponential, while pi is the least positive zero of sine.
- **Semantic role:** Sine, cosine, and pi are callable/ordinary values;
  identities, existence of a positive zero, and periodicity are theorems.
- **Ideal Litex form:** `complex_sin` and `complex_cos` as functions once
  complex exponential selection is available; real sine/cosine as their real
  restrictions; concrete `cosine_taylor_coefficient` and
  `sine_taylor_coefficient` functions whose even/odd support and factorial
  values are explicit; `is_least_positive_sine_zero` as a concrete relation
  followed by a selected `pi` only after unique existence.
- **Nearest wrong alternative:** Treating pi as an arbitrary positive zero
  loses the source definition and makes periodicity too weak. A proposition
  for sine/cosine is unusable in identities.
- **Dependencies:** Complex exponential and arithmetic by `definition`;
  factorials and the Chapter 4 power-series radius/sum/analyticity interfaces
  by `definition/signature`; coefficient selection, the ratio test,
  completeness/infimum, continuity, derivatives, and the intermediate value
  theorem by `proof/trust-source`.
- **Downstream uses:** Theorems 4.7.2/5 and all later Fourier analysis.
- **Allowable hole:** Existence and uniqueness of the parity-indexed
  coefficient values, the ratio-test proof of infinite radius, identification
  of the selected trigonometric values with the displayed series, and
  positive-zero existence/least-zero selection may be trusted, but their
  mathematical specifications stay explicit.
- **Current implementation:** `complex_sin` and `complex_cos` are concrete
  exponential combinations. Because structured unique selection currently
  loses its result carrier, `real_sin` and `real_cos` are selected through
  explicit real-value relations. The planned Taylor coefficient relations
  expose exactly the even terms
  `(-1)^k/(2k)!` and odd terms `(-1)^k/(2k+1)!`; their selected coefficient
  functions feed the existing radius, sum, and real-analytic interfaces.
  `is_least_positive_sine_zero` is concrete and `pi_real` is the selected
  least zero.

### Finite-dimensional calculus and local inversion

- **Ordinary meaning:** Finite-dimensional real vectors carry coordinate
  addition, scaling, and Euclidean distance. A total derivative is a linear
  first-order approximation. A contraction is nonexpansive; a strict
  contraction has a positive contraction constant below one. A strict
  contraction has at most one fixed point, and has exactly one when its
  metric space is nonempty and complete. A map
  that differs from the identity by a one-half Lipschitz perturbation on a
  ball is injective and its image contains the concentric half-radius ball.
  An invertible derivative then yields a genuine local inverse, while a
  nonzero derivative in the dependent coordinate yields a local implicit
  graph.
- **Semantic role:** Vector spaces, zero vectors, Euclidean balls, and
  identity perturbations are callable constructions. Linearity,
  differentiability, injectivity, image containment, local inverse data, and
  implicit graph data are relations on supplied maps and subsets. The
  contraction, inverse-function, and implicit-function results are named
  theorems.
- **Ideal Litex form:** Keep `row_vector_space`, coordinate operations,
  the canonical zero/negation operations, `euclidean_distance`, and
  `euclidean_open_ball` as template-contained functions. Represent column
  vectors by a tagged carrier so that transpose changes presentation without
  falsely making row and column vectors interchangeable. Keep
  `is_standard_basis_vector` as the coordinate graph, expose the source
  vector `standard_basis_vector(j)` by `have fn ... by exist!`, and state the
  finite standard-basis decomposition explicitly. Keep `is_contraction` as
  the factor-one inequality and expose
  `is_strict_contraction_with_factor` plus existential
  `is_strict_contraction` for `0<c<1`. Use concrete `prop`s for the
  one-half perturbation bound,
  pointwise identity perturbation, injectivity on a subset, local inverse
  data, and implicit graph data. Theorems must quantify the source maps,
  domains, base points, derivatives, and neighborhoods and conclude those
  relations explicitly.
- **Interface sketch:**

  ```litex
  prop is_half_lipschitz_perturbation(n N+, ball power_set(\row_vector_space<n>), g fn(x ball) \row_vector_space<n>):
      forall x, y ball:
          \euclidean_distance<n>(g(x), g(y)) <=
              (1 / 2) * \euclidean_distance<n>(x, y)

  prop is_injective_on(X, Y set, f fn(x X) Y):
      forall x, y X:
          f(x) = f(y)
          =>:
              x = y
  ```

- **Nearest wrong alternative:** A theorem asserting only
  `exist inverse ... st {inverse = inverse}` or
  `exist implicit_map ... st {implicit_map = implicit_map}` discards every
  source hypothesis and does not express local invertibility or an implicit
  zero-set graph. Such a statement is not a permissible proof workaround and
  must be replaced rather than wrapped.
- **Dependencies:** Finite coordinate vectors and Euclidean distance by
  `signature/definition`; metric balls and function images by `definition`;
  linear maps and total derivatives by `definition`; completeness and the
  contraction mapping theorem by `proof/trust-source`; the chain rule by
  `proof`.
- **Downstream uses:** Lemma 6.6.6 feeds the inverse function theorem.
  The inverse function theorem supplies the local coordinate change used by
  the implicit function theorem. Immediate probes are evaluating the
  identity-perturbation map, applying injectivity to equal outputs, and
  obtaining a preimage for every point of the half-radius ball.
- **Allowable hole:** The analytic proofs may remain narrowly trusted while
  their hypotheses, neighborhoods, maps, inverse identities, and graph
  conclusions remain concrete. Until dependent selected results can be
  stored, zero, transpose, and standard-basis objects may use concrete graph
  relations plus unique-existence theorems; callers may supply a basis family
  satisfying the graph for decomposition. No tautological self-equality may
  stand in for these interfaces.
- Treating `transpose_row_vector` as another function with exactly the
  `row_vector_space` carrier erases Remark 6.1.4's deliberate distinction
  between row and column spaces. Leaving `e_j` as only a caller-supplied
  relation likewise fails to represent Definition 6.1.5's named vectors and
  makes the following standard-basis expansion unusable.
- **Current implementation:** Vector operations, linearity, matrices,
  derivative relations, contractions, strict contractions, and fixed points
  are concrete. The ordinary and strict contraction predicates are distinct;
  the fixed-point theorems consume only the strict predicate.
  `is_zero_row_vector` and `vector_neg` expose the canonical additive data.
  `column_vector_space` is the tagged carrier
  `cart({1}, row_vector_space<n>)`, and `is_transpose_row_vector` gives its
  concrete graph. Zero, transpose, and each standard basis vector have
  unique-existence theorems; the coordinate-decomposition theorem accepts
  any supplied family satisfying `is_standard_basis_vector`. Callable
  selection is deferred only because the verifier cannot store a result
  whose carrier retains the earlier dimension argument.
  `has_row_vector_space_laws` states coordinate addition commutativity and
  associativity, both zero identities, both additive-inverse identities,
  scalar associativity, both distributive identities, and scalar identity.
  Merely returning the typed sum would duplicate the function signature and
  would not represent Lemma 6.1.2.
  Examples 6.1.7--6.1.9 expose five concrete callable probes:
  `dilation_by_five`, `quarter_turn`, `first_two_coordinate_projection`,
  `zero_extend_inclusion`, and template `identity_transformation`. Rotation
  and inclusion use coordinate graph relations plus selected functions, so
  later developments can evaluate them without replacing the examples by
  bare existential claims.
  Example 6.1.12 similarly keeps its six-entry matrix as selected callable
  data, defines the associated matrix-induced map by the general finite-sum
  formula, and records both expanded output coordinates in
  `is_example_6112_output`.
  `linear_transformation_has_matrix` returns
  unique existence, not only a matrix witness. The matrix-composition theorem
  binds displayed maps to `A`, `B`, and `matrix_product(A,B)` through
  `is_matrix_representation`, then returns the pointwise equation
  `LA(LB(x)) = LAB(x)`. Merely returning the typed matrix product would again
  duplicate a function signature rather than represent Lemma 6.1.16. The
  one-variable derivative bridge is an actual equivalence: its concrete
  relation contains derivative-to-relative-approximation and the converse,
  while the Chapter 3 derivative predicate carries the required limit-point
  clause.
  Example 6.2.3 should expose its base point `(1,2)`, squaring map
  `(x,y) |-> (x^2,y^2)`, derivative candidate `(a,b) |-> (2a,4b)`, and the
  actual `has_total_derivative_at` conclusion. These are selected callable
  objects with coordinate graphs; a bare trusted differentiability sentence
  with unbound maps would not preserve the worked example.
  Example 6.3.4 should reuse those exact objects, add the concrete direction
  `(3,4)`, and expose that the selected derivative map produces `(6,16)` and
  is the one-sided directional derivative there. Re-declaring a detached
  square map or an unconnected result vector would break the source's
  deliberate reuse of Example 6.2.3.
  Example 6.3.9 should be a four-layer reusable probe: the callable map
  `(x,y) |-> (x^2+xy,y^2)`, callable first and second partial-value maps,
  a base-point-indexed derivative action on a direction, and the matching
  `2x2` Jacobian graph. The displayed arbitrary-direction formula must be
  connected to that derivative action; four unrelated trusted formulas would
  not model the example.
  Example 6.4.2 should expose the product rule as a specialization of the
  chain rule, not as a detached scalar identity. Its interface should connect
  two scalar-valued maps, their pairing `h(x)=(f(x),g(x))`, multiplication
  `k(a,b)=ab`, the composite product, the three displayed derivative actions,
  and the final coordinate formula
  `D(fg)(v)=g(x0)Df(v)+f(x0)Dg(v)`. The nearest rejected form is a theorem
  that merely asserts the final equality without binding the pairing,
  multiplication, or composite whose chain-rule derivation the example is
  meant to demonstrate.
  The following unnumbered linear-postcomposition application should likewise
  bind the actual composite `Tf`, its derivative action, and the pointwise
  formula `DTf(v)=T(Df(v))`. A theorem saying only that some derivative exists
  would omit the useful content, while a detached equality would no longer
  certify that the displayed action differentiates the composite. The
  coordinate-curve application should then bind one curve assembled from
  scalar coordinate functions, its velocity assembled from their scalar
  derivatives, the composite with `f`, and the finite partial-derivative sum.
  This keeps the source's chain-rule route visible rather than recording an
  unrelated finite-sum identity.
  Example 6.5.3 should extend the exact callable map from Example 6.3.9 rather
  than introduce a second copy. Its reusable node is one second-partial family
  indexed by derivative coordinate, first-partial coordinate, base point and
  output coordinate. The family should display `(2,0)`, `(1,0)`, `(1,0)` and
  `(0,2)`, certify the existing map as `C2`, and expose the mixed-partial
  symmetry consumed by Clairaut's theorem. Four detached constant-vector
  assertions would preserve the arithmetic but lose the relationship to the
  first partial maps and the `C2` interface.
  Examples 6.6.2 should expose three callable self-maps on their actual
  carriers: translation and halving on `R`, and `x-x^2` on `[0,1]`. The five
  source classifications—translation is nonexpansive but not strict, halving
  is strict, and the quadratic interval map is nonexpansive but not
  strict—should use the same general contraction predicates as Theorem 6.6.4.
  Replacing them by isolated inequalities would make the examples unusable as
  probes of the strict/non-strict distinction introduced in Definition 6.6.1.
  Example 6.8.3 should expose the callable scalar function
  `f(x,y,z)=xy+yz+zx+1`, a relation for its three displayed partial values at
  a supplied surface point, and the local implicit graph solving for `z` when
  `x+y != 0`. The resulting two partials of the implicit function must retain
  the ratios `-(y+z)/(y+x)` and `-(x+z)/(y+x)` and share the exact local graph
  data returned by Theorem 6.8.1. A theorem giving only the two ratios would
  omit the graph-existence claim, while a generic invocation of the implicit
  theorem would omit the worked calculation.
  `contraction_has_at_most_one_fixed_point` records the source's
  unconditional-with-respect-to-completeness uniqueness conclusion for a
  strict contraction. `contraction_mapping_theorem` separately requires a
  nonempty complete carrier before asserting existence and uniqueness.
  `has_total_derivative_at` includes Tao's requirement that the base point is
  a limit point of the domain, expressed directly by a distinct domain point
  in every positive Euclidean neighborhood. The
  former tautological statement of Lemma 6.6.6 has been replaced by concrete
  ball, perturbation, injectivity, and image-containment interfaces. Because
  the direct dependent zero-vector object and its unique selector both fail,
  the checked theorem quantifies an explicit origin satisfying the concrete
  zero-vector relation. Lemma 6.7.1 binds a supplied inverse map through the
  concrete `is_linear_two_sided_inverse` relation and concludes that the
  inverse map is linear; a lower-bound predicate is not a substitute for this
  source statement. The inverse function theorem now quantifies its open
  domain, displayed derivative and linear inverse and returns typed open
  neighborhoods, two-sided local inverse laws, and the inverse-derivative
  formula. The implicit function theorem now uses `k` free coordinates and
  one dependent coordinate and exposes the local zero-set graph and the
  coordinate derivative formula. A callable coordinate-combination map is
  still blocked by nested function-return alias unfolding, so the checked
  interface uses the concrete `is_coordinate_extension` graph relation.

### Outer measure and measurable sets

- **Ordinary meaning:** Outer measure is the infimum of volumes of countable
  open-box covers. It is monotone and countably subadditive but is not
  additive on all subsets of the real line. Caratheodory-measurable sets are
  exactly those that split every test set additively, and on them the
  restriction of outer measure is countably additive.
- **Semantic role:** Box covers, candidate outer-measure values,
  pairwise-disjoint indexed families, and Caratheodory measurability are
  relations. The counterexamples to finite and countable additivity and the
  sigma-algebra/countable-additivity results are named theorems.
- **Ideal Litex form:** Keep boxes and covers as supplied set/function data,
  `has_outer_measure_value` as a candidate-value relation, and define a
  reusable pairwise-disjoint-family predicate. Failure-of-additivity theorems
  must display the family, every member's outer-measure value, the union
  value, the corresponding finite or infinite sum, and their inequality.
  Lemma 7.2.5 must likewise expose all six outer-measure laws over supplied
  data: empty-set value, positivity, monotonicity, finite subadditivity,
  countable subadditivity, and translation invariance. The family laws must
  bind every member value and the actual union value; translation invariance
  must bind a translated set pointwise to the original set and shift.
  Open and closed boxes must each be pointwise set-builder relations tied to
  their lower and upper coordinate bounds. Their outer-measure theorems must
  consume those relations; a volume product alone does not identify a set as
  the corresponding box.
  Examples 7.2.8--7.2.12 should expose concrete one-dimensional rational and
  irrational subsets, the unit interval, its irrational part, the planar
  unit segment, and the full planar x-axis. The current outer-measure
  candidate relation is real-valued, so the source value `+infinity` must be
  represented by an honest unboundedness relation: every real bound is
  exceeded by the finite outer measure of some subset. It must not be encoded
  as an arbitrary real value. The rational-line example must return outer
  measure zero and the short-cover consequence from Remark 7.2.10; the
  irrational examples must return infinite outer measure on the line and
  value one inside the unit interval. The dimension comparison must connect
  the one-dimensional unit interval of value one with the corresponding
  planar segment and the whole planar x-axis of two-dimensional value zero.
  Detached numerical equalities would omit the sets and the dimension whose
  measure is being computed.
  Lemma 7.4.4 must expose its full measurable-set closure package:
  complement; translated-set measurability and equal measure; binary and
  finite unions/intersections; open/closed box measurability; and
  measurability of every outer-measure-zero set. Each constructed set must be
  tied to the source data rather than represented by an arbitrary measurable
  witness.
  Lemma 7.4.2 and Remark 7.4.3 must distinguish lower coordinate half-spaces
  `{x:x_j<t}` from upper coordinate half-spaces `{x:x_j>t}` and return
  measurability for both. A single lower-half-space theorem does not formalize
  the source's displayed `x_n>0` case. Remark 7.4.6 should then expose the
  existence of a genuinely nonmeasurable subset as the consequence of finite
  additivity on measurable sets and Proposition 7.3.3; external discussion of
  choice and Banach--Tarski remains explanatory rather than a new local
  interface.
  Within the current real-valued outer-measure model, Lemma 7.4.8 should state
  the finite-total branch of countable additivity: a pairwise-disjoint
  measurable family with supplied member values and a supplied real series
  total has a measurable union with that same outer-measure value. It must not
  invent a real total for a family whose source sum may be `+infinity`.
  Lemma 7.4.9 must return both countable-union and countable-intersection
  measurability for the same supplied measurable family. Returning only the
  union is not the source sigma-algebra result.
  Lemma 7.4.10 must require the supplied set to be Euclidean open and return
  an exact open-box decomposition, not merely a family that covers it. A
  uniform `N+` family represents the empty case by empty members and a
  finite decomposition by padding the family with empty members.
  Lemma 7.4.11 must use the Euclidean metric from Chapter 6 for both its open
  and closed branches. The discrete metric would make every subset open and
  closed and therefore would not represent the source's Borel property.
  Definition 7.5.1 must quantify only over Euclidean-open codomain sets; asking
  for measurable preimages of every subset is strictly stronger than
  measurability and is not the source definition. Lemma 7.5.2 must require
  metric continuity on the measurable domain, using the Euclidean distance
  restricted to that domain.
  Lemma 7.5.3 must expose both directions of the open-box criterion, not merely
  project measurability of the domain. Corollary 7.5.4 concerns the supplied
  coordinate functions of a Euclidean-valued map; it is not a half-space
  theorem and must bind every coordinate function pointwise to that map.
  Lemma 7.5.5 is closure under a continuous outer function on an open
  intermediate range. It must bind the measurable inner function, continuous
  outer function, range membership, and actual composition; a restatement of
  one inverse-image clause is not the source lemma.
  Corollary 7.5.6 returns measurability of the concrete pointwise transforms
  `abs(f)`, `max(f,0)`, and `min(f,0)`. A theorem about one arbitrary
  superlevel/sublevel threshold is not this corollary.
  Corollary 7.5.7 must include the quotient branch with a pointwise nonzero
  denominator, in addition to sum, difference, product, maximum, and minimum.
  Its inputs and outputs should use the real-valued measurable-function
  interface, not only the later extended-real superlevel shorthand.
  Lemma 7.5.8 is the two-way equivalence between real-valued measurability and
  measurable strict superlevel sets for every real threshold. Null-set
  modification is Exercise 7.5.5 and must not replace this numbered lemma.
  Definition 7.5.9 needs an actual extended-real carrier rather than a
  real-valued function with an extended-real name. Use the tagged values
  `(-1,0)`, `(0,r)`, and `(1,0)` for negative infinity, finite `r`, and
  positive infinity, and define measurability by strict superlevel preimages.
  The source's compatibility sentence must be an explicit bridge: a real
  function is measurable exactly when its pointwise tagged embedding
  `x -> (0,f(x))` is extended-real measurable. Maintaining two predicates
  without this equivalence leaves the Chapter 8 finite/extended boundary
  unjustified.
  Lemma 7.5.10 should use the induced tagged total order, explicit sequence
  and tail suprema/infima, and limsup/liminf defined from those extrema.
  Pointwise convergence is represented by equality of limsup and liminf with
  the supplied limit. The finite-real theorem remains a companion for Chapter
  8 rather than standing in for the source lemma.
- **Nearest wrong alternative:** A conclusion such as
  `exist family ... st {family = family}` or disjoint sets constrained only
  by `A = A` and `B = B` says nothing about outer measure and is not a
  permissible representation of Propositions 7.3.1 or 7.3.3. Positivity and
  monotonicity alone are not a representation of the six-part Lemma 7.2.5.
  Likewise, concluding an outer-measure value for an arbitrary `box` from
  unrelated lower/upper bounds and their volume is not Proposition 7.2.6.
- **Dependencies:** Euclidean coordinate spaces and boxes by
  `signature/definition`; countable covers and real-series sums by
  `definition`; choice/Vitali representatives by `trust/source`; set-family
  unions and finite sums by `definition`.
- **Downstream uses:** The additivity counterexamples motivate
  Caratheodory measurability and prove the existence of nonmeasurable sets.
  Measurable-set closure and countable additivity then feed all of Chapter 8.
- **Allowable hole:** The choice-based counterexample constructions may
  remain theorem-level trusted existentials, but every mathematical witness
  and the failed equality must remain explicit. The current real-valued outer
  measure model does not yet represent `+infinity`; this boundary must remain
  visible rather than silently changing the counterexample.
- **Current implementation:** `has_outer_measure_full_laws` binds the empty
  set, a nested pair, a nonempty finite family, a countable family, and a
  translated set to their supplied outer-measure values, then returns all six
  conclusions of Lemma 7.2.5. The empty family is covered by the separate
  empty-set clause; nonempty finite families use `closed_range(1,count)`.
  `is_closed_box` binds a supplied set to inclusive coordinate bounds, while
  `is_open_box` uses strict bounds; each box-measure theorem consumes the
  corresponding relation. `has_measurable_set_full_laws` packages all six
  parts of Lemma 7.4.4 over a pointwise translated set, actual finite
  set-family union/intersection, concrete open/closed boxes, and a supplied
  outer-null set. `has_countable_measure_additivity_conclusion` binds the
  actual family union to the supplied real series total for the finite-total
  branch of Lemma 7.4.8. `has_measurable_sigma_closure` binds both family
  constructions in Lemma 7.4.9.
  `is_open_box_or_empty` makes the padding case explicit.
  `has_countable_open_box_decomposition` binds every nonempty family member
  to concrete strict coordinate bounds and equates the family union with the
  original open set. `open_and_closed_sets_are_lebesgue_measurable` then uses
  Euclidean openness or closedness rather than the unrelated discrete metric.
  `is_measurable_function` now guards each inverse-image obligation with
  Euclidean openness, and `continuous_function_is_measurable` consumes an
  explicit metric-continuity premise over the restricted domain distance.
  `has_measurability_open_box_equivalence` records both directions of Lemma
  7.5.3. `is_coordinate_function_family` binds each real coordinate to the
  original Euclidean-valued map, and
  `has_measurability_coordinate_equivalence` records both directions of
  Corollary 7.5.4. `is_function_composition_on_open_range` binds the
  intermediate-range membership and pointwise composite used by Lemma 7.5.5;
  `continuous_after_measurable_is_measurable` consumes the corresponding
  measurability, openness, and metric-continuity premises.
  `has_measurable_zero_transforms` packages the three pointwise-bound
  measurable outputs of Corollary 7.5.6; the superlevel-set relation remains
  separate for Lemma 7.5.8 and Definition 7.5.9.
  `is_pointwise_real_quotient` includes the nonzero-denominator obligation,
  and `has_measurable_real_function_algebra` now returns all six measurable
  outputs of Corollary 7.5.7.
  `has_measurability_superlevel_equivalence` records both directions of Lemma
  7.5.8, while `null_modification_preserves_measurability` remains a separate
  exercise-facing theorem. `extended_real` and
  `is_extended_real_measurable` now provide the genuine tagged interface for
  Definition 7.5.9. The extended-real order, sequence/tail extrema, pointwise
  extrema, and limsup/liminf relations now support the source-facing Lemma
  7.5.10. `is_finite_real_superlevel_measurable` names the finite-valued layer
  still consumed by Chapter 8 and its companion real order-limit theorem.

### Nonnegative Lebesgue integration and series

- **Simple-function spine:** Definition 8.1.1 is the property that a
  measurable real function on a measurable domain has finite image. This must
  remain distinct from Lemma 8.1.4, which derives a finite pairwise-disjoint
  measurable characteristic-function decomposition. Lemma 8.1.3 returns both
  the pointwise sum and an arbitrary real scalar multiple as simple
  functions.
- **Nearest wrong alternative:** Defining a simple function directly by an
  arbitrary overlapping measurable cover collapses Definition 8.1.1 into
  Lemma 8.1.4 and does not justify the value-times-measure integral formula.
  Replacing Lemma 8.1.4 with “simple functions are measurable” changes the
  numbered source result entirely; measurability is already an assumption in
  Tao's definition.
- **Implementation order:** finite-value cover relation → simple-function
  predicate → characteristic-function example → algebra-result relation →
  characteristic decomposition → finite simple-integral presentation →
  tagged simple-integral relation. The decomposition carries set containment,
  pairwise disjointness, measurability, indicator laws, and the exact finite
  pointwise sum. Example 8.1.2 consumes the supplied characteristic-function
  relation and returns both measurability and simplicity; it is an example
  theorem, not a second definition of characteristic functions.
- **Integral-domain conditions:** A simple-integral candidate is defined only
  for a nonnegative simple function. A nonnegative Lebesgue-integral candidate
  is defined only for a nonnegative measurable function on a measurable
  domain. These are part of Definitions 8.1.6 and 8.2.2, not optional theorem
  premises supplied only by selected consumers.
- **Finite versus infinite simple integrals:** Definition 8.1.6 must use the
  tagged `[0,+infinity]` carrier, because Example 8.1.7 computes one displayed
  simple integral as `11` and another as `+infinity`. The existing real-valued
  finite-sum presentation therefore remains only the finite companion
  `has_finite_simple_lebesgue_integral`. The source-facing
  `has_simple_lebesgue_integral` has a finite branch embedding that value as
  `(0,value)` and an infinite branch embedding it as `(1,0)` when a positive
  level piece has infinite outer measure. This tagged relation is consumed by
  Definition 8.2.2's upper-bound formulation; downstream formulas that
  explicitly quantify real simple integrals use the finite companion.
- **Example 8.1.7 concrete interfaces:** The two displayed functions remain
  supplied callable functions tied pointwise to Tao's exact cases:
  `3` on `[1,2]`, `4` on `(2,4)`, zero elsewhere; and `1` on `[0,+infinity)`,
  zero elsewhere. Their example theorems return tagged integral values
  `(0,11)` and `(1,0)` respectively. Remark 8.1.8 is explanatory intuition
  about area and introduces no reusable mathematical dependency, so it remains
  prose rather than a detached formal proposition.
- **Remark 8.2.4 compatibility bridge:** Integration on a measurable
  subdomain is represented by an actual restricted function, not by passing a
  subset name to an unchanged-domain integral relation. For a nonnegative
  real simple function, a pointwise tagged embedding into
  `extended_nonnegative_real` connects Definition 8.1.6 to Definition 8.2.2
  at the same tagged value. This is a theorem-level compatibility result, not
  a second definition of either integral. Remark 8.2.3 is comparative prose,
  while Remark 8.2.5 is already subsumed by the positivity and
  positive-infinity branches of Proposition 8.2.6.
- **Remark 8.2.12 moving bump:** The counterexample is a supplied
  `N+`-indexed family tied pointwise to the characteristic functions of
  `[k,k+1)`, together with a supplied zero limit function. The result must
  state pointwise convergence, integral value one for every family member,
  integral value zero for the limit, and the unequal limiting values. It uses
  the finite nonnegative-integral companion because every displayed integral
  is real; this does not weaken the source example. The preceding observation
  that Tonelli needs no convergence hypothesis is already visible in the
  tagged partial-sum supremum interface of Corollary 8.2.11.
- **Post-Definition 8.3.2 consequences:** Consistency with nonnegative
  integration must bind two pointwise-equal views of the same mathematical
  function: one valued in `extended_nonnegative_real` for Definition 8.2.2,
  and one valued in `chap7::extended_real` for the signed integral. When the
  tagged nonnegative integral is `(0,value)`, the signed integral has the real
  value `value`. Formula (8.1) must bind supplied positive and negative part
  functions, the supplied absolute-value function, their finite tagged
  integral representatives, and the signed integral value, then return the
  complete chain
  `abs(signed) <= positive_integral + negative_integral = absolute_integral`.
  A detached inequality over arbitrary real numbers would lose the function
  and integral dependencies; folding this into Proposition 8.3.3 would lose
  its source location and theorem identity.
- **Approximation distinction:** The generic pointwise nondecreasing-to
  relation records order and pointwise convergence and is consumed by
  monotone convergence. Lemma 8.1.5 uses a separate refinement that also
  requires every member of the approximating family to be a simple function.
  Conflating these roles either drops the source's simple-function witnesses
  or incorrectly restricts the general monotone convergence theorem.

- **Ordinary meaning:** The integral of a nonnegative measurable function is
  the supremum of integrals of dominated simple functions. Increasing limits
  commute with this integral, so the integral of a pointwise countable sum of
  nonnegative measurable functions equals the series of their integrals.
- **Semantic role:** Simple-function presentations, candidate integral
  values, pointwise increasing approximations, pointwise series sums, and
  domination are relations. Monotone convergence, additivity, Tonelli for
  nonnegative series, Fatou, and dominated convergence are named results.
- **Ideal Litex form:** Keep integral values explicit rather than selecting a
  global integral function. Definition 8.2.2 uses the tagged carrier
  `[0,+infinity] = ({0} x nonnegative_reals) union {(1,0)}` inherited from
  Chapter 7's extended-real representation. Its source-facing value relation
  is the least tagged upper bound of the embedded real integrals of all
  nonnegative simple minorants; the finite-real relation remains a companion,
  not the definition itself. Proposition 8.2.6 must use tagged positive-scalar
  multiplication, pointwise tagged order, equality outside an explicit null
  set, and tagged domain restriction. Its conclusions are positivity, the
  zero-almost-everywhere equivalence, positive homogeneity, monotonicity,
  almost-everywhere invariance, and restriction monotonicity. Monotone
  convergence must bind every family member
  to its supplied integral value, expose monotonicity of that integral
  sequence, identify a supplied total as its supremum, and give the same total
  as the integral of the pointwise supremum. Fatou must use tagged sequence
  liminf relations for both the pointwise function liminf and the liminf of
  the tagged member-integral sequence; an ordinary metric limit is not a
  substitute. A Tonelli statement must quantify the function family, its
  pointwise sum, the sequence of member integrals, and the series total, then
  identify that total as the integral of the pointwise sum. Extended
  nonnegative addition must expose both the finite branch and the absorbing
  positive-infinity branch. Tonelli's pointwise series and integral series
  must be represented through tagged finite partial sums whose tagged
  suprema are the supplied sum function and total integral. An upper Lebesgue
  integral value must be both a lower bound for all integrable-majorant
  integrals and approximable from above by such integrals; dually, a lower
  Lebesgue integral value must be both an upper bound for all
  integrable-minorant integrals and approximable from below. The epsilon
  witnesses are the concrete `inf`/`sup` content needed by Lemma 8.3.6.
  Absolute integrability and both upper/lower integral relations must also
  retain the source's measurable-domain premise; measurability of function
  superlevel sets alone does not imply that premise in the current Chapter 7
  interface.
- **Nearest wrong alternative:** `exist total R st {total >= 0}` does not
  depend on the function family and expresses neither a pointwise sum nor any
  integral. It is not a representation of Corollary 8.2.11. Likewise, an
  existential sequence of arbitrary real values does not state monotone
  convergence, and `$has_metric_limit(..., integrals, L)` does not state that
  `L` is the liminf of a possibly nonconvergent sequence. Merely requiring an
  upper-integral candidate to be below every majorant integral, or a
  lower-integral candidate to be above every minorant integral, gives only an
  arbitrary bound and does not define the infimum or supremum.
- **Dependencies:** Measurable functions and measurable domains by
  `signature/proof`; simple integrals and nonnegative integrals by
  `definition`; finite additivity and monotone convergence by `proof`; real
  function-series sums by `definition`.
- **Downstream uses:** Fatou's lemma, Borel--Cantelli, signed integration,
  dominated convergence, and Fubini.
- **Allowable hole:** The monotone-convergence proof and the Tonelli
  interchange may remain trusted conclusions, while all pointwise sums,
  member integrals, series values, and equality data remain explicit.
  The source-facing tagged Definition 8.2.2, Proposition 8.2.6, Theorem
  8.2.9, Lemma 8.2.10, Corollary 8.2.11, and Lemma 8.2.13 may coexist with
  clearly named finite-real companions; each finite restriction must stay
  explicit.
- **Current implementation:**
  `is_pointwise_extended_nonnegative_nondecreasing_to` binds the tagged
  increasing function family to its pointwise tagged supremum.
  `has_extended_monotone_convergence_conclusion` records the increasing tagged
  integral sequence, its tagged supremum, and the matching integral of the
  pointwise supremum. The real-valued monotone-convergence relation and
  theorem remain finite companions.
  `has_extended_nonnegative_sum` supplies finite addition and the absorbing
  positive-infinity branch used by `is_pointwise_extended_nonnegative_sum`.
  The source-facing additivity theorem and Tonelli corollary use this same
  relation for function values, integral values, pointwise partial sums, and
  integral partial sums.
  `is_pointwise_real_series_sum` supplies the pointwise series graph used by
  the finite companion `tonelli_for_nonnegative_series`.
  `is_pointwise_extended_nonnegative_liminf` and
  `is_extended_nonnegative_integral_liminf` reuse Chapter 7's tagged
  extended-real sequence-liminf relation in the source-facing Fatou theorem.
  `finite_integral_implies_finite_almost_everywhere` separates the tagged
  finite-integral premise from the null exceptional set on which the function
  may equal positive infinity. `is_in_infinitely_many_sets` quantifies
  membership beyond every positive cutoff, and `borel_cantelli_lemma` gives
  measure zero to the corresponding set-builder when the member measures have
  a finite real series sum.
  `is_real_sequence_supremum`, `is_real_tail_infimum`,
  `is_real_sequence_liminf`, and `is_pointwise_real_liminf` expose the order
  data used by `finite_fatou_lemma`. Both source and finite companions bind the
  pointwise liminf and the liminf of member integrals through their matching
  tail-infimum construction.
  `is_pointwise_finite_absolutely_dominated` supplies the common bound used by
  the finite companion. The source-facing
  `is_pointwise_extended_absolutely_dominated` compares a tagged absolute
  value with a tagged nonnegative dominator, and
  `dominated_convergence_theorem` consumes Chapter 7's tagged pointwise-limit
  relation. Its conclusion includes both the signed integral of the tagged
  pointwise limit and convergence of the real member integrals.
  `has_upper_lebesgue_integral` and `has_lower_lebesgue_integral` include both
  their universal bound clauses and epsilon-close tagged integrable
  majorant/minorant witnesses over the extended-real source carrier. Their
  `has_finite_...` relations preserve the R-valued companions.
  `upper_lower_lebesgue_integral_characterizes_integrability` records the
  resulting common-value criterion rather than an order tautology.
  `has_simple_integral_full_laws`,
  `has_extended_nonnegative_integral_full_laws`, and
  `has_extended_signed_integral_full_laws` preserve the complete source-facing
  law lists over supplied pointwise operations, integral values, null-set
  relations, and domain restrictions. The corresponding finite nonnegative
  and signed law relations and theorems remain explicitly named companions.
  Absolute integrability uses an extended-real function, a tagged
  nonnegative absolute-value function, and an explicitly finite tagged
  integral. Positive and negative parts follow the finite,
  positive-infinity, and negative-infinity branches and likewise have finite
  tagged integrals before defining the real signed value.
  The upper/lower integral relations repeat that domain requirement before
  quantifying their integrable majorants and minorants. The signed integral
  consumes an explicit positive/negative-part decomposition of that same
  function; unrelated nonnegative functions cannot witness its value.
  `extended_nonnegative_real` is the tagged subset of Chapter 7's
  `extended_real` containing finite nonnegative values and positive infinity.
  `is_extended_nonnegative_integral_upper_bound` quantifies over the actual
  simple minorants and their embedded simple-integral values, while
  `has_extended_nonnegative_lebesgue_integral` adds the least-upper-bound
  clause. `has_finite_nonnegative_lebesgue_integral` is the older real-valued
  companion consumed only where the source interface is genuinely R-valued or
  where an explicitly named finite companion is retained.
  Fubini's section-integral functions are required to agree with the
  one-dimensional section integrals only outside explicit null exceptional
  sets. Requiring every section to be integrable would strengthen the source
  theorem and is false for standard null-line examples.
  The comparison paragraph after Proposition 8.4.1 should retain its concrete
  separating example rather than only the general compatibility theorem: the
  rational indicator on `[0,1]` has Lebesgue integral zero but no Riemann
  integral. This is a supplied function constrained pointwise by rational
  membership, not an arbitrary function with the desired conclusions added
  as premises. The example depends on the rational null-set calculation from
  Chapter 7 and the two integral relations.
  Remark 8.5.2 should likewise retain the null vertical-line example that
  explains the theorem's almost-everywhere qualification. The supplied
  two-variable function must be tied to the three source cases on `x=0`, and
  its supplied vertical sections must be tied pointwise to that function.
  Its two-dimensional absolute integral is zero, the section at `x=0` is not
  absolutely integrable, and every section with `x != 0` has integral zero.
  These examples are theorem-level source consequences with localized
  `trust/source` proof edges; neither should be folded into the definitions
  of Riemann integrability or Fubini section data.

### Measurable sequence order limits

- **Ordinary meaning:** Pointwise suprema, infima, limsups, liminfs, and
  pointwise limits of measurable real-valued function sequences are
  measurable.
- **Semantic role:** Sequence upper/lower bounds, extrema, tail extrema,
  limsup/liminf witnesses, and their pointwise lifts are relations. Lemma
  7.5.10 is a named preservation result.
- **Ideal Litex form:** Define reusable real-sequence supremum, infimum,
  tail-supremum, tail-infimum, limsup, and liminf relations in Chapter 7.
  Lift each relation pointwise to a supplied function. The theorem must bind
  every displayed output function to the family; the pointwise-limit clause
  is conditional on Chapter 3's actual pointwise-convergence relation.
- **Nearest wrong alternative:** Declaring an arbitrary supplied `limit`
  measurable merely because every `family(k)` is measurable is false and does
  not represent any of the five source constructions.
- **Dependencies:** Real order by `definition`; pointwise convergence by
  `import`; measurable superlevel sets and countable measurable-set closure by
  `proof`.
- **Downstream uses:** Chapter 8 simple approximation, Fatou, monotone and
  dominated convergence.
- **Allowable hole:** The countable union/intersection proofs may remain one
  localized theorem-level trust, but all order-limit relations and output
  functions must remain explicit.

### Measurable real-function algebra

- **Ordinary meaning:** Sums, differences, products, pointwise maxima, and
  pointwise minima of measurable real functions are measurable.
- **Semantic role:** The five pointwise operation graphs are relations;
  Corollary 7.5.7 is a named preservation result.
- **Ideal Litex form:** Quantify supplied result functions, bind each one
  pointwise to `f` and `g`, require both inputs measurable, and return the five
  measurability facts as one source-facing law package.
- **Nearest wrong alternative:** An unconditional existential for a sum
  function neither uses input measurability nor states any measurability
  conclusion, and omits four source operations.
- **Dependencies:** Real arithmetic/order by `definition`; continuous-map
  composition and measurable preimages by `proof`.
- **Downstream uses:** Positive/negative parts, absolute values, simple
  functions, and signed integration.
- **Allowable hole:** The preservation proof may remain one localized trust;
  operation graphs and all five conclusions must be explicit.

### Several-variable chain rule

- **Ordinary meaning:** If `x0` is interior to the domain of `f`, `f(x0)` is
  interior to the domain of `g`, both maps are differentiable at those points,
  and `f` maps its domain into the domain of `g`, then `g ∘ f` is
  differentiable at `x0` with derivative `Dg ∘ Df`.
- **Semantic role:** Function composition and linear-map composition are
  relations; Theorem 6.4.1 is a named result.
- **Ideal Litex form:** Bind a supplied composed function pointwise on the
  whole source domain, including the codomain membership needed to apply `g`.
  Bind a supplied derivative map by `D(v)=Dg(Df(v))`, then use that exact map
  in the total-derivative conclusion. Retain both source interior-point
  hypotheses explicitly.
- **Nearest wrong alternative:** An existential arbitrary derivative map,
  unconstrained by `Df` and `Dg`, omits the chain-rule formula. A conditional
  composition equation without `f(E) ⊆ F` leaves the composed function
  undefined on part of its declared domain. Omitting either interior premise
  silently broadens the source theorem beyond its stated local hypotheses.
- **Dependencies:** Total-derivative relations and linear transformations by
  `definition`; error estimates by `proof`.
- **Downstream uses:** Higher derivative calculations, inverse derivatives,
  and implicit differentiation.
- **Allowable hole:** The remainder estimate may remain one localized trust;
  both composition graphs and the exact derivative formula must be explicit.

### Continuous partials imply total differentiability

- **Ordinary meaning:** If all coordinate partial derivatives exist on a
  neighborhood of an interior point and are continuous there, then the
  function is totally differentiable at that point. The derivative sends `v`
  to the coordinate sum of `v_j` times the `j`th partial derivative.
- **Semantic role:** A partial-derivative family and the derivative assembled
  from it are relations; Theorem 6.3.8 is a named result.
- **Ideal Litex form:** Quantify `F ⊆ E`, an interior point `x0`, a supplied
  family of partial-derivative values on `F`, and a supplied linear map `L`.
  Require every partial to exist and its coordinate function to be continuous
  at `x0`; bind every coordinate of `L(v)` to the finite sum formula.
- **Nearest wrong alternative:** An unconditional existential total
  derivative for an arbitrary function is false and omits every hypothesis
  and the displayed derivative formula.
- **Dependencies:** Partial derivatives, metric continuity, interior points,
  finite sums, and linear transformations by `definition`; the coordinatewise
  telescoping estimate by `proof`.
- **Downstream uses:** Continuous differentiability, Clairaut, inverse
  function, and implicit function theorems.
- **Current implementation:** `is_partial_derivative_family_on` stores the
  family as scalar coordinates indexed by `(j,x,i)`, then assembles the
  `R^m`-valued partial function anonymously at each use.
  `is_total_derivative_assembled_from_partials` binds the whole row vector
  `L(v)` to the finite coordinate sum. This coordinate presentation avoids
  the current nested-call limitation for a function returning the templated
  `row_vector_space<m>` while preserving the source formula exactly.
- **Allowable hole:** The telescoping/error proof may remain one localized
  trust; the neighborhood, partial family, continuity, and derivative formula
  must be explicit.

### Directional and partial derivatives

- **Ordinary meaning:** Tao's directional derivative at an interior point is
  the one-sided derivative along the positive ray `x0 + t v`, with `t > 0`.
  A coordinate partial derivative instead uses the two-sided line limit
  `t -> 0`, `t != 0`.
- **Semantic role:** Both are candidate-value relations. They do not yet
  introduce selected derivative functions.
- **Ideal Litex form:** `has_directional_derivative` includes the interior
  premise and a positive-ray epsilon-delta condition. A partial derivative
  requires a standard basis vector `e_j`, the directional value `value` along
  `e_j`, and the opposite directional value `-value` along `-e_j`.
- **Interface sketch:**

  ```litex
  prop has_partial_derivative(..., coordinate, value):
      exist basis_vector \row_vector_space<n> st {
          $is_standard_basis_vector(n, coordinate, basis_vector),
          $has_directional_derivative(..., basis_vector, value),
          $has_directional_derivative(
              ..., \vector_scale<n>(-1, basis_vector),
              \vector_scale<m>(-1, value)
          )
      }
  ```

- **Nearest wrong alternative:** Using `0 < abs(t) < delta` for a directional
  derivative silently changes Tao's one-sided definition to a two-sided one.
  After restoring the one-sided definition, using only the `+e_j` direction
  would describe a right partial derivative rather than the source's
  two-sided partial.
- **Dependencies:** Euclidean interior and coordinate vector operations by
  `definition`; total differentiability and linearity by `proof` in Lemma
  6.3.5.
- **Downstream uses:** Partial-derivative families, `C^1`/`C^2`, Clairaut,
  inverse functions, and implicit functions.
- **Allowable hole:** Lemma 6.3.5 may retain one localized proof trust for
  specializing the total approximation to a positive ray. The sign conditions
  and interior premises are part of the interface and may not be weakened.

### Continuously and twice continuously differentiable maps

- **Ordinary meaning:** On an open set, a `C^1` map has every first partial
  derivative and those partial-vector functions are continuous everywhere.
  A `C^2` map is `C^1`, and each first partial-vector function is itself
  `C^1`.
- **Semantic role:** Two nested regularity relations on a supplied function.
  The first-partial coordinate family is witness data, not a selected
  derivative function.
- **Ideal Litex form:** `is_continuously_differentiable` requires openness and
  one coordinate-indexed first-partial family satisfying
  `is_partial_derivative_family_on` and pointwise continuity on the domain.
  `is_twice_continuously_differentiable` reuses that first-order relation and
  supplies one first-partial family whose `j`th vector-valued function also
  satisfies `is_continuously_differentiable`.
- **Nearest wrong alternative:** Requiring only `exist L` with
  `has_total_derivative_at` at every point expresses differentiability, not
  continuity of the first derivative and not the existence or continuity of
  second derivatives. Using the `C^2` predicate in the inverse and implicit
  function theorems also strengthens Tao's `C^1` hypothesis unnecessarily.
- **Dependencies:** Open sets, partial-derivative families, and metric
  continuity by `definition`; Theorem 6.3.8 by `proof` when converting the
  partial presentation to total differentiability.
- **Downstream uses:** Clairaut consumes `C^2`; the inverse and implicit
  function theorems consume only `C^1`.
- **Current implementation:** Clairaut quantifies `f:E -> R^m`. Its supplied
  second-partial family is indexed by the two derivative coordinates, the
  point of `E`, and the output coordinate. Symmetry is asserted for every
  output coordinate; the scalar reduction belongs only to the proof strategy,
  not to the public theorem interface.
- **Allowable hole:** The regularity relations themselves must be concrete.
  Theorems deriving total derivatives or equality of mixed partials may retain
  their existing localized proof debt.

### Periodic complex functions

- **Ordinary meaning:** An `L`-periodic complex function is unchanged by
  translation by `L`, hence by every integer multiple `kL`. A continuous
  one-periodic function belongs to the source space `C(R/Z; C)`.
- **Semantic role:** Periodicity and continuous one-periodicity are
  properties of supplied functions. The Hermitian integral is first a
  candidate-value relation and then a canonical selected complex value.
  Integer-translation invariance and the closure/boundedness laws are
  mathematical results.
- **Ideal Litex form:** Keep `is_periodic_with_period` and
  `is_continuous_one_periodic` as concrete `prop`s. Expose the source Remark
  5.1.3 as a theorem
  `f(x + k*L) = f(x)` for `k Z`; do not encode only positive natural
  translations. Keep algebra outputs as supplied pointwise functions so
  closure statements say which function is accepted. Keep
  `has_periodic_inner_product(f,g,value)` as the coordinate-integral graph and
  add `periodic_inner_product(f,g)` through `have fn ... by exist!` on
  continuous one-periodic inputs. Model the source-defined `L2` norm and
  metric the same way: concrete candidate relations followed by callable
  `periodic_l2_norm(f)` and `periodic_l2_distance(f,g)` selections.
- **Nearest wrong alternative:** Treating the single-step equation as if it
  already exposed arbitrary integer translations leaves the `R/Z` interface
  unusable at negative Fourier frequencies. Returning only function carriers
  for sums or products would repeat signatures without proving continuity or
  periodicity. Leaving the source-defined inner product as only a
  caller-supplied relation prevents ordinary expressions from applying it;
  the same is true of anonymous norm and distance witnesses.
- **Dependencies:** Complex-valued functions and positive real periods by
  `signature`; integer induction/substitution by `proof/trust-source`;
  compactness, continuity algebra, and uniform limits by
  `proof/trust-source`.
- **Downstream uses:** Integer-frequency characters, periodic integration,
  convolution, Fourier coefficients, and symmetric partial sums.
- **Allowable hole:** The positive/negative integer induction, compactness
  proofs, and existence/uniqueness of the coordinate integral, nonnegative
  square-root norm, and induced distance may remain localized trusts, while
  the quantified integer translation, all three canonical selected values,
  and every closure output stay explicit.
- **Current implementation:** The single-period and continuous one-periodic
  predicates are concrete. Boundedness, algebra closure, and uniform-limit
  closure are bundled over supplied functions. The integer-translation
  theorem is explicit. `has_periodic_inner_product` is the concrete
  coordinate-integral graph and `periodic_inner_product` is its callable
  selected value. The `L2` norm and distance also follow the same
  relation/selection split, with checked graph theorems for all three selected
  values.
  Examples 5.1.2 and 5.1.4 should additionally bind their supplied functions
  to the displayed sine, cosine, complex-exponential, identity, constant,
  integer-frequency, and square-wave formulas before asserting periodicity or
  its failure. Their semantic role is concrete function data plus theorem
  results. The nearest rejected form is a theorem quantifying arbitrary
  functions and assuming the desired periodicity, or a list of periodicity
  facts disconnected from the displayed formulas. These examples depend on
  Chapter 4 trigonometric and exponential functions by `definition/import`
  and on their period laws by `proof/trust-source`. They feed the character
  family and the intuition for functions on `R/Z`; their background
  trigonometric-period calculations may remain localized proof debt.

The character of frequency `n` should be defined from the complex exponential
`exp(2*pi*i*n*x)`, with its cosine/sine coordinates exposed as a derived
Euler-formula theorem. Its membership in the continuous one-periodic function
space is a theorem, not a consequence to leave implicit. A detached
`is_character_value` relation that only repeats the coordinate formula and has
no consumers is not part of the intended public interface.

A trigonometric-polynomial presentation lives in `C(R/Z;C)` and must retain
that continuous one-periodic condition alongside its finite character
expansion. Fourier coefficients repeat the inner-product pattern:
`has_fourier_coefficient(f,n,value)` is the candidate graph, while
`fourier_coefficient(f,n)` is the canonical selected value. Leaving only the
graph does not represent the source notation `f_hat(n)` as a callable
construction.

Periodic convolution is likewise a source-defined function, not merely a
pointwise relation supplied by the caller. Keep
`has_periodic_convolution_value(f,g,x,value)` as the coordinate-integral graph
and `is_periodic_convolution_function(f,g,convolution)` as its pointwise
lifting. The ideal public interface then selects the unique whole function
`periodic_convolution(f,g)` for continuous one-periodic `f,g`, with a checked
graph theorem. Existence and uniqueness may remain one localized trust until
the real integral construction, function extensionality, and periodic closure
are connected.

Remark 5.5.2 distinguishes three convergence levels for the actual symmetric
Fourier partial sums. Reuse Chapter 3's metric pointwise and uniform
convergence predicates rather than inventing Fourier-specific copies. Express
real-line differentiability of a complex-valued function through supplied
real and imaginary coordinate functions and their supplied derivatives;
continuous differentiability uses Chapter 3's
`has_continuous_derivative_on` on both coordinates. The remark's two negative
claims and its differentiable/continuously-differentiable implications are
source-facing proof boundaries, even though their proofs are explicitly
beyond the book's scope.

### Fourier coefficient families and symmetric partial sums

- **Ordinary meaning:** A continuous one-periodic function has one Fourier
  coefficient at each integer frequency. Its `N`th symmetric Fourier partial
  sum is the finite sum from `-N` through `N`. The Fourier theorem concerns
  this particular sequence, not an arbitrary sequence of trigonometric
  polynomials. Absolute summability of the same coefficients yields uniform
  convergence, and Plancherel identifies their squared magnitudes with the
  squared periodic `L2` norm.
- **Semantic role:** Fourier coefficients and symmetric partial sums are graph
  relations over supplied coordinate families. Absolute summability and
  the Plancherel energy identity are properties. Fourier convergence and
  Plancherel are named theorems.
- **Ideal Litex form:** Keep real and imaginary coefficient coordinates
  explicit until complex-valued selection and finite complex sums are stable.
  Character orthonormality must include both the Kronecker-delta inner-product
  value and the source's unit-`L2`-norm conclusion for every character.
  A Fourier theorem must return coefficient coordinates and a partial-sum
  family tied to them pointwise. Uniform convergence must assume absolute
  summability of those coordinates. Plancherel must conclude, rather than
  assume, convergence of the actual squared-magnitude energy series. Until a
  direct integer-indexed bilateral series is available, pair the positive and
  negative frequencies in one `N+` term and keep the zero-frequency term
  visible:

  ```litex
  exist total R st {
      $chap3::has_real_series_sum(
          fn(k N+) R {
              chap4::complex_abs((coefficient_re(k), coefficient_im(k)))^2
              + chap4::complex_abs((coefficient_re(-k), coefficient_im(-k)))^2
          },
          total
      ),
      total + chap4::complex_abs(
          (coefficient_re(0), coefficient_im(0))
      )^2 = norm^2
  }
  ```

  Package this exact conjunction as
  `has_plancherel_energy_identity(coefficient_re,coefficient_im,norm)` so the
  theorem can return one stable mathematical relation rather than restating a
  parser-sensitive nested existential.

- **Nearest wrong alternative:** `exist partial_sums ... st
  is_l2_convergent_to(partial_sums,f)` permits an arbitrary constant sequence
  and does not mention Fourier coefficients. Likewise, an arbitrary
  `coefficient_energy` sequence whose total is `norm^2` does not state
  Plancherel. Requiring a supplied energy sequence to be summable as a
  hypothesis also omits the theorem's convergence conclusion.
- **Dependencies:** Periodic inner products and characters by `definition`;
  trigonometric-polynomial coordinate formulas by `definition`; periodic
  Weierstrass approximation and orthogonality by `proof`; real-series and
  uniform-convergence relations by `definition`.
- **Downstream uses:** Pointwise and uniform Fourier convergence criteria,
  Parseval/Plancherel identities, and later harmonic-analysis interfaces.
- **Allowable hole:** The approximation and orthogonality arguments may remain
  theorem-level trusted conclusions, while the coefficient family,
  symmetric-partial-sum equations, Plancherel summability conclusion, and
  energy identity must be explicit.
- **Current implementation:** `has_periodic_l2_pair_laws` packages all five
  conclusions of Lemma 5.2.7 over supplied sums, scalar multiples, inner
  products, and norm values. `has_trigonometric_polynomial_coefficient_recovery`
  packages the in-range coefficients, zero coefficients outside the range,
  and finite Parseval identity. The later Fourier interfaces consume the same
  coordinate coefficients through explicit symmetric restrictions.
  `has_periodic_inner_product_full_laws` similarly packages all of Lemma
  5.2.5, with each linearity identity connected to supplied pointwise
  operations and candidate integral values.
  `has_character_orthonormality` packages both inner-product cases and the
  unit-norm clause of Lemma 5.3.5.
  `has_continuous_periodic_function_laws` packages the boundedness,
  algebra-closure, and uniform-limit clauses of Lemma 5.1.5 over explicit
  pointwise operations and a supplied uniformly convergent family.
  Periodic convolution is represented by a whole-function graph over its
  pointwise integral values. Lemma 5.4.4 consumes the supplied sums, scalar
  multiples, and convolution functions and exposes closure, commutativity,
  both additive laws, and the three equal scalar placements. Merely proving
  closure of one arbitrary convolution function is not the source lemma.
  A periodic approximation to the identity is a continuous one-periodic
  complex function with an explicitly real coordinate view, not an unrelated
  real function satisfying only positivity and integral bounds. Plancherel
  directly returns convergence of the paired positive/negative
  squared-coefficient series together with the zero-frequency-adjusted energy
  identity; it no longer assumes a caller-supplied convergent energy sequence.

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

typed map + two metric functions
  --definition--> epsilon-delta control at a point
epsilon-delta control
  --definition--> continuity at a point
continuity at every point
  --definition--> continuity on a space
metric limits + metric open/closed sets
  --proof/trust-source--> continuity characterizations
pointwise continuity
  --proof--> composition continuity

function limit relation --definition--> sequential/neighborhood forms
pointwise convergence --definition--> function-family limits
uniform convergence --proof--> pointwise convergence
uniform convergence + continuity --proof/trust-source--> continuous limit

bounded functions + real supremum
  --existence/uniqueness/selection--> uniform distance
uniform distance --definition--> sup norm
uniform convergence --proof--> convergence in uniform distance
continuous bounded functions + complete codomain
  --proof/trust-source--> complete function space

finite sum --definition--> function partial sums
function partial sums + uniform convergence
  --definition--> uniformly convergent function series
sup norm + complete function space
  --proof/trust-source--> Weierstrass M-test

Riemann integral background + uniform convergence
  --proof/trust-source--> interchange limit and integral
derivative background + uniform derivative convergence
  --proof/trust-source--> differentiable uniform limit

polynomial + support + Riemann integral
  --existence/uniqueness/selection--> convolution
approximation kernels + convolution
  --proof/trust-source--> polynomial approximation on [0,1]
zero extension + affine rescaling
  --proof--> Weierstrass approximation on [a,b]

coefficient sequence + center + finite sum
  --definition--> power-series partial sums
coefficient root limsup + infinity tag
  --definition/trust-source--> radius of convergence
power-series convergence on a neighborhood
  --definition--> real analyticity
analyticity + derivative tower
  --proof/trust-source--> Taylor coefficients and uniqueness
boundary series + summation by parts
  --proof/trust-source--> Abel continuity
two analytic coefficient sequences
  --definition/proof--> Cauchy-product coefficients
factorial + selected power-series sum
  --existence/selection--> real exponential
real exponential bijection
  --existence/uniqueness/selection--> logarithm
cart(R,R) + real arithmetic
  --definition--> complex operations, conjugation, modulus, distance
complex exponential
  --definition--> sine and cosine
sine positive-zero set + infimum
  --existence/uniqueness/selection--> pi

finite coordinate vectors + finite sums
  --definition--> Euclidean distance and balls
one-half Lipschitz perturbation + identity perturbation
  --definition--> perturbation map on a ball
complete closed ball + contraction mapping theorem
  --proof/trust-source--> injectivity and half-ball image containment
total derivative + invertible linear map + perturbation lemma
  --proof/trust-source--> local inverse data
local inverse data + chain rule
  --proof/trust-source--> implicit zero-set graph

countable open-box covers + box volumes
  --definition--> outer-measure candidate values
Vitali representatives + pairwise disjoint translates
  --choice/trust-source--> finite/countable additivity counterexamples
outer measure + Caratheodory splitting
  --definition--> measurable sets
measurable-set closure + disjoint families
  --proof/trust-source--> countable additive Lebesgue measure

simple functions + measurable partitions
  --definition--> simple integral candidate values
simple integral suprema
  --definition--> nonnegative integral candidate values
nonnegative finite additivity + monotone convergence
  --proof/trust-source--> Tonelli for pointwise nonnegative series
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
8. Chapter 2 continuity: define epsilon--delta control, pointwise continuity,
   and domain continuity before the sequential, open-set, composition,
   product, compactness, and connectedness results.
9. Chapter 3 function limits, pointwise convergence, and uniform convergence.
10. Bounded-function spaces, uniform distance, completeness, partial sums, and
    the sup norm.
11. Uniform-limit interchange with integration and differentiation.
12. Polynomial/support vocabulary, convolution, approximation kernels, and
    the staged Weierstrass approximation theorem.
13. Formal power-series terms, partial sums, tagged radii, and analyticity.
14. Derivative towers, Taylor coefficients, Abel boundary limits, and
    Cauchy-product multiplication.
15. Real exponential and logarithm.
16. Concrete complex coordinate arithmetic, metric laws, and exponential.
17. Sine, cosine, least positive zero, pi, and periodicity.
18. Periodic complex functions, Hermitian integration, characters,
    trigonometric polynomials, convolution, and Fourier convergence.
19. Finite real coordinate spaces, linear maps, total derivatives,
    contractions, and local inverse/implicit maps.
20. Open boxes, countable covers, outer measure, Caratheodory measurable sets,
    and measurable functions.
21. Simple functions, nonnegative integration, signed integration,
    convergence theorems, Riemann compatibility, and Fubini.

## Interface decisions and permissible gaps

- Preserve the explicit carrier and callable distance in every public
  interface; do not replace them with a proposition-only metric object.
- Keep candidate limits, convergence, and selected limits separate.
- Keep set-valued topology constructions callable.
- Use `N+` as the canonical sequence index for this module and record the
  source's arbitrary-start convention in comments.
- Keep compactness sequential and prove open-cover compactness as a theorem.
- Source-deferred proofs may be trusted only at the exact result or substep
  the source omits. Full source proofs that remain blocked require an exact
  working note and smallest identified missing interface.
- `ComplexNumber` is a concrete two-field `struct`. This is the ideal reusable form because
  later complex analysis consumes `.real_part` and `.im` directly. The nearest wrong
  form is an opaque equality predicate or an abstract complex-number carrier:
  either would hide coordinate computation. Addition and multiplication
  commutativity are checked from their formulas. Nested function returns do
  not always retain enough struct/alias type information for later projection
  or application; Chapters 4--6 therefore use explicit coordinate relations
  and record the verifier behavior rather than changing the kernel.
- Riemann integration and differentiation use concrete local
  tagged-partition and epsilon--delta definitions. A future stable cross-book
  dependency may replace these definitions only after the Analysis I project
  itself is a clean import.
- One-sided real limits now wrap the Chapter 3 metric function-limit
  relation, and the restricted interval records the direction of approach.
  Complex limit laws use named pointwise sequence operations and concrete
  metric-limit conclusions. Real sine and cosine are selected from concrete
  coordinate graphs of the complex exponential. This is the intended
  downstream-facing design. Complex-exponential convergence is now the
  concrete limit of coordinate recurrences for powers and partial sums.

## Metric axiom reformulation layer

- Remark 1.1.3 should be a checked theorem over the existing
  `is_metric_space(X, dist)` interface: zero distance is equivalent to point
  equality. This is preferable to adding a second metric predicate whose laws
  would duplicate Definition 1.1.2. Its nearest rejected form is a trusted
  result package, because both directions follow immediately from the current
  identity and separation clauses.
- Remark 1.1.10 should not be represented by a vacuous predicate saying that
  the already named `l1`, `l2`, and `linf` distances are “special.” A useful
  future interface needs a genuine exponent carrier containing finite
  `p >= 1` and an infinity point, together with the parameterized finite-sum
  formula and its infinity specialization. Until that layer is used
  downstream, retain the remark as an explicit modeling todo.

### Chosen finite-p and infinity interface

- Use `lp_finite_exponent = {p R: p >= 1}` for finite exponents and keep the
  infinity metric as a separate endpoint. A family predicate must contain the
  finite-sum power formula for every finite `p`, identify `p=1` and `p=2`
  with the existing l1 and l2 distances, and identify the separate endpoint
  with linf. This makes Remark 1.1.10 mathematically usable without pretending
  that real `p` literally contains infinity.

### Shared shortest-path system

- Examples 1.1.12 and 1.1.13 should share one path-system interface containing
  endpoints, nonnegative length, constant paths, reversal, concatenation, and
  a selected shortest path for every pair. The induced distance is the length
  of that selected path. These operations explain identity, symmetry, and the
  triangle inequality.
- The sphere example specializes the carrier to the unit sphere in
  three-dimensional real coordinate space and interprets paths as curves.
  The network example keeps an arbitrary connected computer carrier and
  interprets path length as a positive number of connections. Their geometric
  or graph-specific existence claims may remain trusted, but the common
  interface must not assume `is_metric_space` as an input.

## Elementary ball and point-classification consequences

- Remark 1.2.4 should reuse the callable `metric_ball` and prove two facts:
  positive-radius balls contain their center, and increasing the radius gives
  a superset. The center theorem already exists; the monotonicity theorem
  should expose the exact subset relation rather than introduce another ball
  object. Its nearest rejected form is a trusted result package, since both
  facts are elementary consequences of the defining inequality.
- Remark 1.2.6 should reuse `is_metric_interior_point`,
  `is_metric_exterior_point`, and `is_metric_boundary_point`. Its public
  consequences are: interior points belong to the set, exterior points do
  not, and no point is both interior and exterior. Boundary membership itself
  remains deliberately undecided. The nearest rejected form is a new
  classification predicate duplicating Definition 1.2.5.

## Metric-dependent limit counterexample

- Remark 1.1.21 should retain the concrete carrier `[0,1]`, the reciprocal
  sequence, and the endpoint-swapping bijection. The second distance is the
  pullback of the usual distance along that swap, not an arbitrary supplied
  metric. The public result should say that the same sequence tends to `0`
  under the restricted usual metric and to `1` under the pullback metric.
- The ideal reusable intermediate node is a general pullback-metric theorem:
  an injective map into a metric space induces a metric. The nearest rejected
  form is a proposition merely assuming that the swapped distance is a
  metric, since that would erase the explanation of the example. For the
  current source slice, keep the concrete swap and localize any missing
  bijection or epsilon calculation as proof debt.

## Intrinsic compactness and boundedness compatibility

- Remark 1.5.2 should expose compactness of `Y` using only the carrier `Y`
  and the restricted metric. The ambient formulation
  `is_metric_compact(X, dist, Y)` and the self-carrier formulation on `Y`
  have the same sequence/subsequence content and should be connected in both
  directions rather than represented as two unrelated assumptions.
- For boundedness, the ideal intrinsic node is a uniform pairwise distance
  bound on `Y`. The ambient-ball formulation in Definition 1.5.3 quantifies
  over centers in `X`; equivalence with the pairwise formulation needs a
  nonempty witness from `Y` (with the empty set handled separately) and the
  triangle inequality. The nearest rejected form is to claim ambient
  independence merely because both predicates are named “bounded.”
- Remark 1.5.4 should compare usual-metric boundedness of a real subset with
  the order-theoretic existence of lower and upper real bounds. Keep this
  order-bounded predicate local and concrete. Its downstream uses are the
  Heine--Borel statements; any missing absolute-value or witness arithmetic
  should remain a localized theorem debt, not be folded into the definition.
