# Mathematical Collections

## Purpose and scope

This standalone module demonstrates one complete specification-proof-code
line for Newton's method applied to `x^2 - 2 = 0`. Its central result is not
a same-formula wrapper equality: the recursive trajectory directly calls the
function selected for Python/C extraction, and Litex proves a quadratic
residual contraction plus a closed-form rate bound for that trajectory.

Floating-point error analysis and an epsilon-style limit theorem are outside
scope. The implemented exact inequalities are sufficient to expose the
quadratic rate without claiming IEEE-754 behavior.

## Modeling conventions

`newton_sqrt_two_step` is total on `R` because executable extraction currently
uses an ordinary `R -> R` interface. The zero branch returns one. The
mathematical trajectory starts from one, and a checked invariant proves every
iterate is at least one, so convergence reasoning uses only the ordinary
Newton branch.

The residual `x^2 - 2`, rather than distance to an assumed square-root
constant, is the error measure. This keeps every quantity algebraic and lets
the one-step square identity lead directly to a quadratic rate.

## Mathematical spine

### Residual

- **Ordinary meaning:** the equation error `x^2 - 2` for a candidate square
  root of two.
- **Semantic role:** real-valued function.
- **Ideal Litex form:** `have fn`.
- **Interface sketch:** `have fn square_root_two_residual(x R) R = x^2 - 2`.
- **Nearest wrong alternative:** assuming a named `sqrt(2)` value would add an
  unnecessary interface and proof dependency.
- **Dependencies:** real arithmetic.
- **Downstream uses:** the residual gap and one-step square identity.
- **Allowable hole:** none; the function and all uses verify.

### Total executable Newton step

- **Ordinary meaning:** `(x + 2/x)/2` away from zero, with an explicit restart
  value at zero.
- **Semantic role:** function and executable boundary.
- **Ideal Litex form:** `algo … by cases` (defines the mathematical fn and the extractable cases together).
- **Interface sketch:** `algo newton_sqrt_two_step(x R) R by cases: ...`.
- **Nearest wrong alternative:** maintaining a separate positive-real
  same-formula function would force a trivial bridge while the convergence
  theorem should constrain the exact extracted function.
- **Dependencies:** real arithmetic and exhaustive zero/nonzero cases.
- **Downstream uses:** the recursive iterate, the residual identity, and
  Python/C extraction.
- **Allowable hole:** target floating-point semantics are outside exact-real
  verification.

### Recursive Newton trajectory

- **Ordinary meaning:** `x_0 = 1` and `x_(n+1) = newton_sqrt_two_step(x_n)`.
- **Semantic role:** sequence function.
- **Ideal Litex form:** recursive `have fn` by induction.
- **Interface sketch:** `have fn sqrt_two_newton_iterate(n N) R by induc ...`.
- **Nearest wrong alternative:** a host-language-only loop would disconnect
  the convergence theorem from the extracted step.
- **Dependencies:** the total executable step.
- **Downstream uses:** positivity invariant, residual gap, and rate theorems.
- **Allowable hole:** none; the recurrence verifies.

### Trajectory invariant

- **Ordinary meaning:** every iterate beginning at one satisfies `x_n >= 1`.
- **Semantic role:** reusable mathematical result.
- **Ideal Litex form:** named `thm`, proved by induction.
- **Interface sketch:** `forall n N: sqrt_two_newton_iterate(n) >= 1`.
- **Nearest wrong alternative:** assuming nonzero denominators at each step
  would hide the reason the totalized zero branch is unreachable.
- **Dependencies:** the recursive definition and the positive-input inequality
  `newton_sqrt_two_step(x) > 1`.
- **Downstream uses:** the exact step identity at each iterate and the factor
  bound `4*x_n^2 >= 4`.
- **Allowable hole:** none; both the step inequality and induction verify.

### Residual gap and comparison bound

- **Ordinary meaning:** `g_n = |x_n^2 - 2|` and
  `B_n = 4 * (1/4)^(2^n)`.
- **Semantic role:** two sequence functions.
- **Ideal Litex form:** `have fn`.
- **Interface sketch:** `sqrt_two_newton_gap(n)` and
  `sqrt_two_newton_gap_bound(n)`.
- **Nearest wrong alternative:** listing a few numerical iterates would show
  examples but not establish a rate for arbitrary `n`.
- **Dependencies:** residual, iterate, absolute value, and exponentiation.
- **Downstream uses:** the quadratic contraction and closed-form induction.
- **Allowable hole:** none; both definitions verify.

### Quadratic convergence rate

- **Ordinary meaning:** the exact identity
  `4*x_n^2*g_(n+1)=g_n^2` yields `g_(n+1)<=g_n^2/4`, and comparison with
  `B_(n+1)=B_n^2/4` yields `g_n<=B_n`.
- **Semantic role:** main mathematical results.
- **Ideal Litex form:** named `thm` declarations.
- **Interface sketch:** `sqrt_two_newton_gap_contracts_quadratically` and
  `sqrt_two_newton_gap_is_bounded`.
- **Nearest wrong alternative:** proving only that the step agrees with
  another same-formula function says nothing about convergence speed.
- **Dependencies:** one-step residual identity, trajectory invariant, bound
  recurrence, and induction.
- **Downstream uses:** concrete certified bounds such as `g_2 <= 1/64`.
- **Allowable hole:** an epsilon-style limit theorem is not claimed; the
  exact double-exponential inequality itself is fully checked.

## Dependency map

Edge legend: `definition` means the body uses the dependency, `proof` means a
theorem derives from it. The `algo` statement both defines the mathematical
function and stores its extractable cases.

```text
real arithmetic --definition--> square_root_two_residual
real arithmetic + zero cases --definition--> newton_sqrt_two_step (algo by cases)
newton_sqrt_two_step --definition--> sqrt_two_newton_iterate
sqrt_two_newton_iterate + step inequality --proof--> x_n >= 1
residual + iterate --definition--> g_n
step formula + residual --proof--> one-step residual-square identity
x_n >= 1 + residual-square identity --proof--> quadratic contraction
comparison recurrence + contraction --proof--> closed-form rate bound
```

There are no axiom, `trust`, or external-source boundary nodes.

## Intended build order

Define the residual and the exact executable step (`algo … by cases`) first.
Define the recursive trajectory directly from that step. Establish
the positive invariant before specializing the one-step identity to the
trajectory. Derive quadratic contraction, prove the comparison recurrence,
and finish with the closed-form induction and the two-step bound.

## Interface decisions and permissible gaps

Keep one Newton step interface: the same `newton_sqrt_two_step` is executable
and appears in the mathematical recurrence. Its total zero policy remains
visible rather than being smuggled into a premise. Do not interpret the
exact-real bound as a floating-point proof. A future floating-point showcase
would need a separate rounding and overflow model; it must not silently reuse
this theorem as if Python `float` were `R`.
