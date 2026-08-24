# Mathematical Design: School Mathematics in a Nutshell

## Purpose and scope

This module is a standalone, one-file tour through every mathematical
direction mapped by `scripts/high_school_book/textbook/Introduction.lit`. It is
not a second textbook and does not duplicate all 20 chapters. Each direction
instead contributes one core interface, named result, or worked calculation
that shows how later mathematics would use that subject.

The module uses native carriers and operations whenever they already express
the mathematics. Formula-defined maps and set-valued constructions are
`have fn`; judgments about supplied objects are `prop`; important reusable
results are `thm`. No concept is encoded through `trust`, a local axiom, or a
wrapper type created only for this showcase.

## Core interface cards

### 1. Sets, logic, and number sense

- **Meaning:** membership, subset, finite cardinality, and gcd provide the
  foundational language for collections and elementary arithmetic.
- **Form:** native facts over finite sets and the builtin `gcd` object.
- **Rejected form:** a custom finite-set or divisibility structure would
  duplicate existing carriers.
- **Use:** `2 $in {1,2,3}`, `{1,2} $subset {1,2,3}`, and `gcd(84,30)=6`.

### 2. Algebra, powers, and logarithms

- **Meaning:** equations isolate unknowns; factorization identifies roots;
  inequalities compare quantities; exponentials and logarithms encode growth.
- **Form:** source-facing `thm` declarations for equation solving and AM-GM,
  formula-defined arithmetic and geometric means, and native power/log facts.
- **Rejected form:** an `is_solution` wrapper would merely rename equality,
  while a relation around a proposed mean would prevent direct calculation.
- **Dependencies:** real arithmetic, nonzero division, square root, order, and
  nonnegative squares.
- **Use:** solve a linear equation, split a factorized quadratic, compare the
  means of `9` and `16`, and calculate `log(2,8*4)`.

### 3. Functions

- **Meaning:** a function is a rule that can be evaluated; identities such as
  `f(-x)=f(x)` classify its behavior.
- **Form:** `have fn linear_function` and `have fn square_function`.
- **Rejected form:** a function-value relation would force every caller to
  introduce an output witness instead of writing `f(x)`.
- **Use:** evaluate a line at two inputs and prove that the square function is
  even.

### 4. Trigonometry

- **Meaning:** radians measure angles, trigonometric functions satisfy the
  Pythagorean identity, and the cosine law computes a triangle side.
- **Form:** `have fn radians_from_degrees`, a formula-defined cosine-law value,
  and native sine/cosine facts.
- **Rejected form:** source-specific wrappers around `sin` and `cos` would
  duplicate the builtin trigonometric surface.
- **Use:** convert `180` and `60` degrees and recover the squared hypotenuse
  `25` from sides `3`, `4`, and a right angle.

### 5. Plane vectors and analytic geometry

- **Meaning:** coordinate pairs support vector addition, dot products, and
  squared norms; geometric loci are sets of points satisfying equations.
- **Form:** `have fn` operations on `cart(R,R)`, `prop perpendicular2`, and
  set-valued circle and ellipse functions.
- **Rejected form:** custom point/vector structs and relation-only loci would
  duplicate Cartesian products or make a circle unusable as a set.
- **Use:** add vectors, detect perpendicular axes, and check points on a circle
  and an ellipse.

### 6. Complex numbers

- **Meaning:** a complex number has real and imaginary coordinates;
  conjugation flips the imaginary sign and modulus measures distance to zero.
- **Form:** native `C`, `i`, `re`, `img`, and `C_abs`, plus
  `have fn complex_conjugate`.
- **Rejected form:** a custom complex struct would conflict with the native
  scalar carrier and lose builtin arithmetic.
- **Use:** compute the coordinates and modulus of `3+4i`, then prove the
  coordinate equations for conjugation.

### 7. Solid geometry and measurement

- **Meaning:** triples model spatial points and directions, coordinate
  equations describe planes, and dimension formulas calculate measurements.
- **Form:** `have fn dot3`, a set-valued `horizontal_plane`,
  `prop point_on_plane`, and formula-defined surface-area/volume functions.
- **Rejected form:** an abstract incidence predicate with no point-set model
  would hide the coordinate witness used by the example.
- **Use:** identify perpendicular coordinate directions, place a point in the
  plane `z=0`, and calculate a prism volume and cube surface area.

### 8. Probability

- **Meaning:** uniform probability counts favorable outcomes; conditional
  probability and Bayes' formula update a probability from a condition or
  evidence.
- **Form:** formula-defined `have fn` values with finite-set and positive-
  denominator conditions in their parameter types.
- **Rejected form:** an opaque probability-space object is unnecessary for
  these small explicit calculations.
- **Use:** the even outcomes of a fair die have probability `1/2`, followed by
  concrete conditional and Bayes calculations.

### 9. Statistics and data analysis

- **Meaning:** mean, variance, and range summarize one dataset; covariance and
  regression compare paired data.
- **Form:** formula-defined `have fn` values over three observations, with the
  nonzero-variance condition attached to the regression slope.
- **Rejected form:** a generic dataset structure would add packaging without
  helping these transparent three-point calculations.
- **Use:** the paired data `(1,2,3)` and `(2,4,6)` has covariance `4/3` and
  regression slope `2`.

### 10. Sequences, induction, and combinatorics

- **Meaning:** closed formulas generate arithmetic and geometric sequences;
  factorial counts permutations; induction proves a statement for every
  natural number.
- **Form:** `have fn arithmetic_term`, `geometric_term`, and
  `permutation_count`, plus a source-facing induction `claim`.
- **Rejected form:** a sequence struct is unnecessary for single closed forms,
  while an unquantified binomial identity would leave its variables undefined.
- **Use:** evaluate fourth terms, count five-object arrangements, expand a
  binomial square, and prove `2^n >= n+1` by induction.

### 11. Derivatives and elementary calculus

- **Meaning:** a difference quotient measures average change; a derivative
  formula vanishes at a stationary point.
- **Form:** `have fn average_change_rate`, named model functions, and
  `prop stationary_point_for_derivative`.
- **Rejected form:** the showcase does not pretend that a supplied derivative
  formula is a checked limit construction; the full book owns that relation.
- **Use:** the circumference function has constant difference quotient
  `2*pi`, and the supplied derivative formula for the quadratic model vanishes
  at `x=3`.

## Dependency mainline

Edge legend: `signature` means a carrier appears in an interface;
`definition` means a formula uses the dependency; `proof` means a result is
derived from earlier facts.

```text
native N, Z, R, C, sets, cart, arithmetic
  -> sets, gcd, equations, powers, logarithms                 [signature/proof]
  -> formula-defined functions and means                     [definition]
  -> trigonometry -> cosine-law example                      [definition/proof]
  -> plane vectors -> circles and ellipses                   [definition]
  -> complex coordinates -> conjugation and modulus          [definition/proof]
  -> spatial triples -> planes and measurement               [definition]
  -> finite sets -> probability                              [definition]
  -> means -> variance and covariance -> regression slope    [definition]
  -> powers and factorial -> sequences, counting, induction  [definition/proof]
  -> functions and division -> average change rate           [definition]
```

The graph is acyclic and follows the reader order in `main.lit`. The showcase
has no import or trust edge; every definition and example is checked in the
standalone module context.
