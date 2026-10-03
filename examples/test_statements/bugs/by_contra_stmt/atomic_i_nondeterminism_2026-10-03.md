# Identical squared-i contradiction proof varies across runs

Task: controlled baseline during classified contra work, 2026-10-03.
Scope: ByContraStmt / existing atomic proof search under an inconsistent local assumption.
Ownership: category 2 candidate; exact calculation/equality-search owner and
scope are still under diagnosis. No false mathematical conclusion was established.

```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

Repeated fresh-process runs produce both success and failure in the frozen
before binary, an isolated current-source build with this task's production
changes reverted, and the after binary. Strict and non-strict controls both
vary. A single earlier before/after difference was therefore insufficient
to attribute a regression to this task. Keep this actual nondeterminism open;
do not change global equality/search policy before its owner is established.

The same target has a shorter accepted authoring route:

```litex
by contra:
    ? i != 0
    impossible i = 0
```

That route passes all 20 strict samples in each of the three binaries.
It preserves the original target; it does not repair or close the original
proof-search nondeterminism. Next action: expose the actual failed proof-step
or closing side, then inspect literal arithmetic and equality representative
selection under the reverse `i = 0` assumption.

[Controlled source/binary comparisons and every sampled output](../../proof_journals/by_contra_atomic_controlled_comparison_2026-10-03.json).
