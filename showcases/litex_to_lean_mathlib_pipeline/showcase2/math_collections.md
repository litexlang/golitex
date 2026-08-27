# Mathematical collection: real sequential completeness

## Public Litex interface

| Declaration | Mathematical meaning | Depends on |
| --- | --- | --- |
| `is_sequence_tail_close_to_limit(a, L, epsilon, n0)` | every term after `n0` is within `epsilon` of `L` | real absolute value and order |
| `converges_to(a, L)` | `a` converges to the supplied real limit `L` | tail closeness |
| `is_convergent_sequence(a)` | `a` has a real limit | `converges_to` |
| `is_cauchy_tail(a, epsilon, n0)` | every pair of terms after `n0` is within `epsilon` | real absolute value and order |
| `is_cauchy_sequence(a)` | every positive tolerance admits a Cauchy tail | Cauchy tail |

## Carrier and trust boundary

The Mathlib-side theorem is intentionally restricted to the generated
`seq(R)` vocabulary. It does not claim that all Cauchy sequences in arbitrary
metric spaces converge.

The five source definitions are transparent and verifier-checked. There is no
Litex theorem asserting completeness and no reserved verifier certificate.
The handwritten Lean consumer proves the corresponding statement using
Mathlib's completeness theorem for `ℝ`; that proof is not imported back into
the Litex verifier.

Trust inventory:

- source `axiom`: none;
- source `trust`: none;
- Lean `axiom`, `sorry`, or `admit`: none in this showcase path;
- Litex completeness foundation for builtin `R`: currently missing;
- Mathlib-side foundational dependency: Lean's kernel plus Mathlib's proved
  `CompleteSpace ℝ` instance.
