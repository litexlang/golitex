# Mathematical Design: Middle-School Mathematics in a Nutshell

## Purpose and scope

This module is a linear tour through recognizable secondary-school
mathematics, informed by the checked examples in
`scripts/high_school_book/textbook/`. It is deliberately a nutshell rather
than another textbook: each stop contributes one classic example, and all
examples live in one `main.lit`.

The implemented order is number sense, equations, inequalities, functions and
sequences, coordinate geometry, then probability and statistics. Trigonometry,
calculus, solid geometry, combinatorics, and a full curriculum hierarchy remain
outside this first version.

## Core interface cards

### Native arithmetic

- **Meaning:** ordinary integer and real calculations form the entry point.
- **Form:** builtin objects and direct facts, including `gcd(84, 30)`.
- **Rejected form:** a local gcd certificate or custom divisibility hierarchy;
  the native `gcd` object already expresses the example.
- **Use:** the opening concrete calculation and all later numeric examples.

### Linear and factorized equations

- **Meaning:** isolate an unknown in a nondegenerate linear equation and read
  the roots of a zero product.
- **Form:** two source-facing `thm` declarations over native real arithmetic.
- **Rejected form:** an `is_solution` predicate that merely renames equality.
- **Use:** `3*2-6=0` and `(3-2)(3-3)=0`.

### Arithmetic and geometric means

- **Meaning:** the two standard means and the inequality between them.
- **Form:** formula-defined `have fn` values plus `thm two_variable_am_gm`.
- **Rejected form:** a relation around a proposed mean value; callers need to
  calculate the means directly.
- **Dependencies:** real order, square root, and nonnegative squares.
- **Use:** the concrete pair `9,16`.

### Linear functions and arithmetic sequences

- **Meaning:** a line is evaluated pointwise, while an arithmetic sequence has
  constant adjacent difference.
- **Form:** `have fn linear_function` and `have fn arithmetic_term`.
- **Rejected form:** structs for a single formula-defined function or sequence.
- **Dependencies:** real arithmetic and positive-natural indices.
- **Use:** `linear_function(4)=14` and the difference law at arbitrary `n`.
- **Verifier boundary:** the two sequence applications are stated before their
  subtraction because the current verifier does not replay both definitions
  through that compound expression automatically.

### Coordinate distance

- **Meaning:** squared Euclidean distance makes the 3-4-5 triangle a coordinate
  calculation.
- **Form:** `have fn distance_sq` over native `cart(R,R)`.
- **Rejected form:** a custom point struct, which would duplicate Cartesian
  products and coordinate projections.
- **Use:** `distance_sq((0,0),(3,4))=25` and `3^2+4^2=5^2`.

### Uniform probability and elementary statistics

- **Meaning:** count favorable outcomes in a finite sample space, then compute
  the mean and range of three data values.
- **Form:** formula-defined `have fn` interfaces over native finite sets and
  real arithmetic.
- **Rejected form:** opaque probability or dataset structures for these small
  calculations.
- **Use:** an even result on a fair die has probability `1/2`; the data
  `2,4,6` has mean `4` and range `4`.

## Dependency mainline

```text
native N/Z/R, gcd, sets, and arithmetic
  -> linear and factorized equations                [proof]
  -> arithmetic/geometric means -> AM-GM            [definition, proof]
  -> linear_function -> arithmetic_term             [definition]
  -> cart(R,R) -> distance_sq -> 3-4-5              [signature, definition]
  -> finite_set_size -> uniform_probability         [well_definedness, definition]
  -> mean3 and range3                               [definition]
```

The graph is intentionally a reader order, not a web of branches. Every node
is checked without direct `trust`, local axioms, or imports from the larger
high-school textbook.
