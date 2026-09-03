# Mathematical system design

This document records the concepts that make the Euclidean geometry showcase
reusable. It is organized by dependency and interface role, not as an
exhaustive theorem index.

## Design spine

```text
coordinate carrier
  → computational operations
  → domain predicates
  → representation bridges
  → reusable geometric results
  → independent problem consumers
```

The governing choice is to keep public statements geometric while making the
coordinate representation available to proofs. This is a small mathematical
system because later work can reuse its vocabulary and laws without rebuilding
their foundations inside each theorem.

## Core concepts and interfaces

### Euclidean points

- **Meaning:** points in the real affine plane.
- **Why it matters:** every later object has one concrete carrier, so tuple
  coordinates and real arithmetic are available without a separate coercion
  layer.
- **Litex form:** `have points set = cart(R, R)`.
- **Nearest rejected form:** an opaque local `Point` with no checked bridge to
  real coordinates; that would make the advertised coordinate proof route
  unavailable.
- **Dependencies:** built-in real numbers and Cartesian products.
- **Downstream uses:** vectors, lines, circles, all geometric predicates, and
  Problem 217.
- **Boundary:** the system models only the two-dimensional real plane; it is
  not an axiomatic or dimension-independent Euclidean geometry interface.

### Computational geometry operations

- **Meaning:** `vec`, `dot`, `det`, and `distance_sq` expose translation,
  orthogonality, orientation/area, and metric information.
- **Why it matters:** these operations reduce geometry to explicit real
  equalities that Litex can inspect and reuse.
- **Representative signatures:**

  ```litex
  have fn vec(A, B cart(R, R)) cart(R, R)
  have fn dot(u, v cart(R, R)) R
  have fn det(u, v cart(R, R)) R
  have fn distance_sq(A, B cart(R, R)) R
  ```

- **Nearest rejected form:** defining distance immediately with a square root;
  that would add positivity and root-normalization obligations to routine
  algebraic proofs.
- **Dependencies:** Euclidean points and real arithmetic.
- **Downstream uses:** coordinate formulas, congruence, perpendicularity,
  collinearity, circle criteria, and affine elimination.
- **Boundary:** `distance_sq` is the primary metric interface; ordinary
  nonnegative distance is not developed as a separate first-class object.

### Geometric predicates

- **Meaning:** stable domain-facing vocabulary such as `is_collinear`,
  `is_right_angle`, `is_parallel`, `is_perpendicular`,
  `are_segments_congruent`, `are_angles_congruent`, `is_on_line`, and
  `is_midpoint`.
- **Why it matters:** consumers state geometry rather than repeat coordinate
  equations.
- **Representative signature:**

  ```litex
  prop is_right_angle(p, q, r cart(R, R)):
      p != q
      r != q
      dot(vec(q, p), vec(q, r)) = 0
  ```

- **Nearest rejected form:** defining a fresh right-angle or midpoint predicate
  in each problem file; that would split one mathematical concept across
  incompatible local interfaces.
- **Dependencies:** computational geometry operations and point
  nondegeneracy conditions.
- **Downstream uses:** reusable geometry theorems and source-facing problem
  statements.
- **Boundary:** angle equality is encoded through normalized dot-product data;
  the module does not construct a first-class real angle value.

### Affine constructions

- **Meaning:** lines, segments, rays, extensions, affine combinations,
  midpoints, centroids, perpendicular feet, and rotations.
- **Why it matters:** geometry problems often depend on where a point is
  constructed, not only on metric equalities.
- **Representative signature:**

  ```litex
  prop is_affine_combination(p, a, b cart(R, R), t R):
      p[1] = (1 - t) * a[1] + t * b[1]
      p[2] = (1 - t) * a[2] + t * b[2]
  ```

- **Nearest rejected form:** treating incidence as an unexplained primitive;
  the Problem 217 proof needs a usable affine witness.
- **Dependencies:** points, vectors, and real parameters.
- **Downstream uses:** line membership, midpoint results, Stewart's theorem,
  projections, and the worked problem.
- **Boundary:** some construction-existence facts remain explicit axioms; the
  current module is strongest at checking properties of supplied points.

### Representation bridges

- **Meaning:** lemmas that translate domain predicates and vector expressions
  into coordinate equalities and translate the resulting facts back.
- **Why it matters:** without this layer, every consumer would have to unfold
  the complete representation manually.
- **Representative interfaces:** `vec_coordinate_formula`,
  `dot_coordinate_formula`, `det_coordinate_formula`,
  `distance_sq_coordinate_formula`, and
  `on_line_implies_affine_parameter`.
- **Nearest rejected form:** one giant theorem-specific algebra block with no
  reusable intermediate interfaces.
- **Dependencies:** computational operations, predicates, and polynomial real
  arithmetic.
- **Downstream uses:** cosine/Pythagorean laws, circle and congruence results,
  affine midpoint arguments, and Problem 217.
- **Boundary:** two algebraic normalization bridges are still declared as
  axioms: `cancel_subtraction_in_sum` and `collinear_to_standard_det`.

### Reusable Euclidean results

- **Meaning:** results about midpoints, congruence, similarity, collinearity,
  perpendicularity, circles, rotations, centroids, and projections.
- **Why it matters:** a mathematical system earns reuse when a later theorem
  cites established results instead of reconstructing its foundations.
- **Representative signatures:** `cosine_law`, `pythagorean_theorem`,
  `sas_congruence`, `concyclic_det_criterion`, and
  `common_line_feet_preserve_midpoint`.
- **Nearest rejected form:** presenting the library as complete Euclidean
  geometry; important existence results and higher theorems remain outside
  the checked core.
- **Dependencies:** predicates and representation bridges.
- **Downstream uses:** problem-specific proof libraries and educational
  geometry developments.
- **Boundary:** `main.lit` currently contains 15 named axioms. Besides the two
  normalization bridges, they include incomplete orthocenter, AAS,
  perpendicular-bisector, rotation, triangle-inequality, median, and point
  construction results.

### Problem 217 as a consumer

- **Meaning:** a real theorem stated with geometric concepts and proved with
  the system's coordinate/affine interfaces.
- **Why it matters:** it tests whether the abstraction boundary survives a
  multi-step downstream proof.
- **Representative signature:** `thm problem_217_midpoint` in
  `problem_217_midpoint.lit`.
- **Nearest rejected form:** replacing the geometric theorem statement with a
  list of raw coordinate equations merely to make the proof easier.
- **Dependencies:** segment congruence, right angles, extensions, line
  incidence, dot/determinant identities, affine parameters, and midpoint
  folding.
- **Downstream uses:** a template for translating other school-geometry
  problems against one shared library.
- **Boundary:** the problem file introduces no additional axiom or trust, but
  the project is checked relative to the explicit axioms already published by
  `main.lit`.

## Publication and proof boundaries

- `main.lit` is a flattened publication artifact; a larger maintained library
  may later split concepts by dependency without changing their public names.
- The project has no `trust` statement and no `abstract_prop`, but it is not
  axiom-free: 15 declarations are explicitly marked `axiom`.
- The Litex runner checks the ordered module relative to those axioms. No Lean
  artifact in this repository independently rechecks the resulting theorem
  graph.
- The closest next proof-debt work is to replace the two algebraic
  normalization axioms, then re-evaluate which higher geometry axioms become
  derivable from the checked coordinate layer.
