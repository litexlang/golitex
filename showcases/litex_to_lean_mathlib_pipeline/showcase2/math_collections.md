# Mathematical collection: real sequential completeness

## Public Litex interface

| Declaration | Mathematical meaning | Depends on |
| --- | --- | --- |
| `is_sequence_tail_close_to_limit(a, L, epsilon, n0)` | every term after `n0` is within `epsilon` of `L` | real absolute value and order |
| `converges_to(a, L)` | `a` converges to the supplied real limit `L` | tail closeness |
| `is_convergent_sequence(a)` | `a` has a real limit | `converges_to` |
| `is_cauchy_tail(a, epsilon, n0)` | every pair of terms after `n0` is within `epsilon` | real absolute value and order |
| `is_cauchy_sequence(a)` | every positive tolerance admits a Cauchy tail | Cauchy tail |
| `cauchy_sequence_converges` | every Cauchy sequence in `seq(R)` converges | real sequential completeness |

## Carrier and trust boundary

The theorem is intentionally restricted to `seq(R)`. It does not claim that
all Cauchy sequences in arbitrary metric spaces converge.

The five source definitions are transparent and verifier-checked. The final
Litex theorem uses the typed builtin theorem
`real_cauchy_sequence_converges`; the verifier checks the real-sequence
carrier and the exact five-definition contract before issuing its certificate.
The Lean consumer turns that certificate into a proof using Mathlib's
completeness theorem for `ℝ`.

Trust inventory:

- source `axiom`: none;
- source `trust`: none;
- Lean `axiom`, `sorry`, or `admit`: none in this showcase path;
- foundational dependency: Lean's kernel plus Mathlib's proved
  `CompleteSpace ℝ` instance.
