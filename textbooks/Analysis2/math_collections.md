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
      f fn(x X) Y, a X, epsilon R_pos, delta R_pos
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
      forall epsilon R_pos:
          exist delta R_pos st {
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
          fn(j N_pos: j <= 2) R {
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
  `prop`s over `N_pos`-indexed function families.
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
  `is_radius_of_convergence` as the Cauchy--Hadamard candidate relation; and
  `is_real_analytic_at`/`is_real_analytic_on` as concrete `prop`s.
- **Nearest wrong alternative:** Encoding every radius as a real silently
  discards infinite radius. Treating a formal power series as a proposition
  prevents later chapters from evaluating terms or partial sums. Making
  analyticity an opaque assumption hides its neighborhood and coefficient
  witnesses.
- **Dependencies:** Natural-index finite sums and real powers by
  `definition`; extended limsup and the infinity convention by
  `trust/source`; Chapter 3 pointwise/uniform series convergence by
  `definition`; differentiation and integration by `trust/source`.
- **Downstream uses:** The radius theorem, analytic derivatives, Taylor
  coefficients, Abel boundary continuity, multiplication, exponential,
  logarithm, and trigonometric series.
- **Allowable hole:** The source's extended-real limsup interface and the
  major exercise-deferred convergence/differentiation proofs may remain
  explicit trust boundaries. The partial sums and analytic witnesses must be
  concrete.
- **Current implementation:** `formal_power_series_data`,
  `power_series_term`, `power_series_partial_sum`, the tagged
  `power_series_radius`, convergence relations, and analyticity predicates are
  concrete. The radius relation and Theorem 4.1.6 proof conclusions remain
  explicit boundaries.

### Iterated derivatives and Taylor data

- **Ordinary meaning:** The zeroth derivative is the original function and the
  `(k+1)`st derivative is the derivative of the `k`th. Analyticity supplies
  every derivative and identifies each coefficient with the derivative value
  divided by a factorial.
- **Semantic role:** A derivative tower is callable family data with a law
  relation; `is_k_times_differentiable` and `is_smooth` are properties.
- **Ideal Litex form:** quantify a supplied derivative tower
  `derivatives fn(k N) fn(x E) R`, constrain its zeroth member and successive
  derivative steps, and state Taylor identities against that tower. Do not
  introduce a global derivative selector before the Analysis I derivative API
  is available.
- **Nearest wrong alternative:** A recursive proposition that cannot expose
  `f^(k)(x)` is unusable in Taylor's formula. A trusted global derivative
  function would conceal existence and domain conditions.
- **Dependencies:** Chapter 3's explicit derivative relation by
  `trust/source`; factorial and finite products by `definition`; analytic
  power-series witnesses by `definition`.
- **Downstream uses:** Propositions 4.2.6, Corollaries 4.2.7/10/12, and the
  exponential and trigonometric derivative identities.
- **Allowable hole:** Successive differentiation laws remain trusted until
  the concrete Analysis I API is connected.
- **Current implementation:** `is_derivative_tower`,
  `is_k_times_differentiable`, recursive `factorial_real`, and the
  multiplication-based derivative-coefficient relation are concrete. The
  derivative and Taylor theorem conclusions remain trusted.

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
  relations are selected interfaces. `ComplexNumber` has concrete `re` and
  `im` fields and concrete addition, negation, multiplication, conjugation,
  modulus, reciprocal/quotient, distance, powers, and exponential
  constructions. Algebraic, metric, and limit laws remain trusted.

### Trigonometric functions and pi

- **Ordinary meaning:** Sine and cosine are defined from the complex
  exponential, while pi is the least positive zero of sine.
- **Semantic role:** Sine, cosine, and pi are callable/ordinary values;
  identities, existence of a positive zero, and periodicity are theorems.
- **Ideal Litex form:** `complex_sin` and `complex_cos` as functions once
  complex exponential selection is available; real sine/cosine as their real
  restrictions; `is_least_positive_sine_zero` as a concrete relation followed
  by a selected `pi` only after unique existence.
- **Nearest wrong alternative:** Treating pi as an arbitrary positive zero
  loses the source definition and makes periodicity too weak. A proposition
  for sine/cosine is unusable in identities.
- **Dependencies:** Complex exponential and arithmetic by `definition`;
  completeness/infimum, continuity, derivatives, and the intermediate value
  theorem by `proof/trust-source`.
- **Downstream uses:** Theorems 4.7.2/5 and all later Fourier analysis.
- **Allowable hole:** Positive-zero existence and least-zero selection may be
  trusted, but the least-positive-zero specification stays explicit.
- **Current implementation:** `complex_sin` and `complex_cos` are concrete
  exponential combinations. Because structured unique selection currently
  loses its result carrier, `real_sin` and `real_cos` are selected through
  explicit real-value relations. `is_least_positive_sine_zero` is concrete
  and `pi_real` is the selected least zero.

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
