# Mathematical Design: Elementary Algebra and Inequalities

## Implemented first-version slice

`main.lit` now checks the mean definitions and AM-GM, linear isolation, the
real quadratic formula, and the radical-equation flagship. The file
deliberately exposes nonnegative square-root premises and contains no direct
`trust`.

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

### Quadratic formula

- **Meaning:** every real root of `a*x^2+b*x+c=0` is one of the two standard
  formula values when `a != 0` and the discriminant is nonnegative.
- **Form:** reusable `thm quadratic_formula`, returning the two candidates as
  a disjunction.
- **Dependencies:** real arithmetic, square root, difference-of-squares
  factorization, zero-product cases, and division by `2*a`.
- **Use:** direct candidate generation for the radical-equation example.
- **Boundary:** it does not construct complex roots when the discriminant is
  negative and is not a general polynomial-solving API.

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
  -> AM-GM                                        [proof]
  -> completed square and zero-product cases      [proof]
  -> quadratic_formula                            [interface]
  -> radical-equation domain and candidate roots  [well_definedness, proof]
  -> unique valid root                            [proof]
```

No canonical root-selection function or general polynomial solver belongs in
this project. The quadratic theorem exposes the standard real formula under
its natural domain conditions, and the flagship theorem consumes it in one
transparent problem.
