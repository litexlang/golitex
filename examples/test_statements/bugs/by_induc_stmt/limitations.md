# ByInducStmt: automatic carrier regression closed

Task: conversation clarification and retest, 2026-10-04. Scope: ordinary and
strong induction goal WD. Current-source behavior closes the earlier automatic
carrier question; no additional maintainer choice is needed.

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
```

This unchanged input now passes, as does the strong-induction variant. `n` is
a bound placeholder over integers at least the starting value. With start 0,
checked integer and nonnegative-bound facts supply natural-number membership.
The current `infer_weak_integer_lower_bound_in_n` rule was implemented by a
concurrent workspace task; this clarification task tested it, not authored it.

Explicit `n $in N` also passes. Starting at -1 with the same N-valued function
and claiming `n / n = 1` from 0 still reject. No trust, global search reset or
weakened domain was introduced here. The original positive Rust assertion is
preserved and passes in the full Rust run.

[Current acceptance and original inputs](../../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).
[Historical failure snapshot](../../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#induction).
[Canonical OBJ10](../../../../plan/src收尾总清单.md#obj10).
