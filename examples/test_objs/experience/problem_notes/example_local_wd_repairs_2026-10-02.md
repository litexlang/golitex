# Local example WD repairs

Task: repair clear local issues from the version-migration example scan.
Scope: finite extrema and finite fold WD in golitex.

```litex
let bad_max = finite_set_max({i})
let bad_min = finite_set_min({i})
```

Both previously passed despite the real-element contract. The finite extrema
owner now requires `S $subset R` using the existing checked subset producer.
These are the original `finite_set_max-N03` and `finite_set_min-N03` corpus
controls; both now reject. Their negatives remain collected after concurrent
corpus promotion removed the old gap/todo labels.

```litex
let bad = finite_set_reduce({0, 1}, fn(x {2}) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

The fold owner now checks set inclusion in the iterand parameter domain and
checks its declared predicates with the existing aggregate producer. Valid
literal/checked/named iterands still pass; failed declarations leave no binding.
Exact before execution was not captured for this new fold-domain probe; the
omission was diagnosed from source and the after rejection was executed.

Acceptance artifacts: [extrema](../../../wd/finite_extrema_real_carrier.lit),
[fold domain](../../../wd/finite_set_fold_domain.lit). Focused release test:
`cargo test --release wd_obligation_tests -- --nocapture` (12 passed).
The [journal](../../../test_statements/proof_journals/example_local_repairs_2026-10-02.json)
retains commands, source versions, negative controls and rejected AC candidate.

Reusable lesson: require every operation's established domain at its owning WD
boundary; a valid signature alone does not cover the operation's input set.
Do not close the separate unordered-fold AC gap with a check that also rejects
legitimate addition or multiplication. That candidate was reverted and the gap
remains open.

Latest shared-source boundary: `0 > 0` now overflows its stack, also affecting the
invalid predicate fold. The wrong-set rejection and valid fold still work.
The snapshot gate is historical acceptance evidence, not a current all-green
predicate gate. This new order-verification regression is retained in the audit.
