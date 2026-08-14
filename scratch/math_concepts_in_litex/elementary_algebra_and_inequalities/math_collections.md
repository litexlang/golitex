# Mathematical Design: Elementary Algebra and Inequalities

## Implemented first-version slice

`main.lit` now checks the mean definitions and AM-GM, linear isolation,
factorization with zero-product cases, an absolute-value equation, and the
planned radical-equation flagship. The file deliberately exposes the
nonnegative-radicand premise before `sqrt` and contains no direct `trust`.

## Core interface cards

### Arithmetic and geometric means

- **Meaning:** standard two-variable means used by the first inequality spine.
- **Form:** `have fn`; callers calculate `arithmetic_mean(x, y)` and
  `geometric_mean(x, y)`.
- **Sketch:** `have fn geometric_mean(x, y R: x >= 0, y >= 0) R = sqrt(x*y)`.
- **Rejected form:** a proposition saying that a proposed value is the mean;
  the value is formula-defined and should be directly applicable.
- **Dependencies:** real arithmetic, order, square root well-definedness.
- **Use:** AM-GM and later small optimization examples.

### Equation solution relation

- **Meaning:** a supplied value satisfies an equation or small system.
- **Form:** normally a direct premise/equality, not a new global `prop` for
  every equation.
- **Rejected form:** a universal `is_solution` wrapper that only renames `=`.
- **Use:** proofs should expose transformations on the original equality.

### Absolute-value bound

- **Meaning:** connects `abs(x) <= r` with the interval `-r <= x <= r` for
  nonnegative `r`.
- **Form:** important reusable `thm`, with `abs` remaining Builtin.
- **Dependencies:** order and cases on the sign of `x`.
- **Use:** inequalities and domain constraints.

The first version instantiates this proof pattern on `abs(x - 3) = 2`; the
fully reusable interval equivalence remains a later library candidate.

### Zero-product bridge

- **Meaning:** a product equal to zero forces a factor to vanish.
- **Form:** use Builtin support directly if it is explanatory and stable;
  otherwise one named `thm`, not a new predicate.
- **Use:** quadratic equations and extraneous-root filtering.

## Main dependency DAG

```text
Builtin R/order/sqrt
  -> arithmetic_mean, geometric_mean              [signature, definition]
  -> square nonnegativity                         [proof]
  -> factorization and zero-product bridge        [proof]
  -> AM-GM                                        [proof]
  -> radical-equation domain and candidate roots  [well_definedness, proof]
  -> unique valid root                            [proof]
```

No canonical root-selection function or general polynomial solver belongs in
this project. The flagship theorem proves one transparent problem, not an API
for arbitrary equations.
