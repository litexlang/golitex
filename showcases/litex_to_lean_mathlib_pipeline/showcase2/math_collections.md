# Mathematical collection: real sequential completeness

## Public Litex interface

| Declaration | Mathematical meaning | Depends on |
| --- | --- | --- |
| `is_sequence_tail_close_to_limit(a, L, epsilon, n0)` | every term after `n0` is within `epsilon` of `L` | real absolute value and order |
| `converges_to(a, L)` | `a` converges to the supplied real limit `L` | tail closeness |
| `is_convergent_sequence(a)` | `a` has a real limit | `converges_to` |
| `is_cauchy_tail(a, epsilon, n0)` | every pair of terms after `n0` is within `epsilon` | real absolute value and order |
| `has_cauchy_tail(a, epsilon)` | some tail is epsilon-Cauchy | Cauchy tail |
| `is_cauchy_sequence(a)` | every positive tolerance admits a Cauchy tail | Cauchy tail |
| `is_eventual_lower_bound(a, B)` | `B` lower-bounds some tail of `a` | tail order |
| `cauchy_sequence_converges` | every real Cauchy sequence converges | real LUB completeness |

## Carrier and trust boundary

The Mathlib-side theorem is intentionally restricted to the generated
`seq(R)` vocabulary. It does not claim that all Cauchy sequences in arbitrary
metric spaces converge.

All source definitions and the sequential-completeness proof are
verifier-checked. The only foundational step is the kernel-owned LUB theorem for
builtin `R`; sequential completeness itself is an ordinary Litex theorem. The
handwritten Lean consumer independently proves the native statement using
Mathlib's completeness theorem for `ℝ`.

Trust inventory:

- source `axiom`: none;
- source `trust`: none;
- Lean `axiom`, `sorry`, or `admit`: none in this showcase path;
- Litex completeness foundation for builtin `R`: kernel-owned LUB theorem;
- sequence-specific builtin theorem: none;
- generated Lean support for every local proof step: deferred and fail-closed;
- Mathlib-side foundational dependency: Lean's kernel plus Mathlib's proved
  `CompleteSpace ℝ` instance.
