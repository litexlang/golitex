# Mathematical Collections

## Purpose and scope

This standalone module demonstrates one complete specification-proof-code
line for Newton's method applied to `x^2 - 2 = 0`. Its central result is not
a same-formula wrapper equality: the checked trajectory calls the function
selected for Python/C extraction, and Litex proves a concrete exact residual
bound after two steps from `1`.

Floating-point error analysis and a general-`n` rate theorem are outside the
current source-only shape. The exact unrolling is enough to keep one shared
definition for proof and extraction without claiming IEEE-754 behavior.

## Modeling conventions

`newton_sqrt_two_step` is total on `R` because executable extraction currently
uses an ordinary `R -> R` interface. The zero branch returns one. The checked
trajectory starts from one and the explicit unrolled values stay above one, so
the residual calculation uses only the ordinary Newton branch.

The residual `x^2 - 2`, rather than distance to an assumed square-root
constant, is the error measure. This keeps every quantity algebraic.

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
- **Downstream uses:** residual evaluations on the unrolled trajectory.
- **Allowable hole:** none; the function and all uses verify.

### Total executable Newton step

- **Ordinary meaning:** `(x + 2/x)/2` away from zero, with an explicit restart
  value at zero.
- **Semantic role:** function and executable boundary.
- **Ideal Litex form:** `algo … by cases` (defines the mathematical fn and the
  extractable cases together).
- **Interface sketch:** `algo newton_sqrt_two_step(x R) R by cases: ...`.
- **Nearest wrong alternative:** maintaining a separate positive-real
  same-formula function would force a trivial bridge while the residual bound
  should constrain the exact extracted function.
- **Dependencies:** real arithmetic and exhaustive zero/nonzero cases.
- **Downstream uses:** the unrolled trajectory and Python/C extraction.
- **Allowable hole:** target floating-point semantics are outside exact-real
  verification.

### Concrete two-step trajectory

- **Ordinary meaning:** `x0 = 1`, `x1 = step(x0) = 3/2`,
  `x2 = step(x1) = 17/12`.
- **Semantic role:** explicit applications of the extracted step.
- **Ideal Litex form (blocked today without kernel change):** recursive
  `have fn … R by induc`, plus `forall n` rate theorems by induction.
- **Current workable form:** exact unrolling in the proof body.
- **Interface sketch:** `newton_sqrt_two_step(1)`, `newton_sqrt_two_step(3/2)`.
- **Nearest wrong alternative:** a host-language-only loop would disconnect
  the residual bound from the extracted step.
- **Dependencies:** the total executable step and residual.
- **Downstream uses:** the concrete residual comparison at step two.
- **Allowable hole:** general-`n` induction remains deferred until
  `have fn … R by induc` and nested `forall`/`by induc` binder reuse work.

### Concrete residual bound at step two

- **Ordinary meaning:** `|x2^2 - 2| = 1/144 <= 1/64`, where `1/64` is the
  comparison value `4 * (1/4)^(2^2)`.
- **Semantic role:** main checked consequence in this showcase.
- **Ideal Litex form:** named `thm` for all `n` with closed-form bound `B_n`.
- **Current workable form:** chained equalities and a positive-difference
  comparison in the file body.
- **Nearest wrong alternative:** proving only that the step agrees with
  another same-formula function says nothing about the residual size.
- **Dependencies:** residual and two applications of the extracted step.
- **Downstream uses:** the extract-facing punchline of the showcase.
- **Allowable hole:** an epsilon-style limit theorem is not claimed.

## Dependency map

Edge legend: `definition` means the body uses the dependency, `proof` means a
theorem derives from it. The `algo` statement both defines the mathematical
function and stores its extractable cases.

```text
real arithmetic --definition--> square_root_two_residual
real arithmetic + zero cases --definition--> newton_sqrt_two_step (algo by cases)
newton_sqrt_two_step + residual --proof--> explicit x1, x2 residuals
explicit residuals --proof--> |x2^2 - 2| <= 1/64
```

There are no axiom, `trust`, or external-source boundary nodes.

## Intended build order

Define the residual and the exact executable step (`algo … by cases`) first.
Unroll two applications of that step from `1`. Establish the residual values
and finish with the comparison against `1/64`.

## Interface decisions and permissible gaps

Keep one Newton step interface: the same `newton_sqrt_two_step` is executable
and appears in the mathematical unrolling. Its total zero policy remains
visible rather than being smuggled into a premise. Do not interpret the
exact-real bound as a floating-point proof. A future floating-point showcase
would need a separate rounding and overflow model; it must not silently reuse
this theorem as if Python `float` were `R`.
