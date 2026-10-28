# Field multiplication dependencies

Distributing over `zero+zero` makes `a*zero` equal to its own sum with
itself; additive inverses then give `a*zero=zero`. Commutativity gives the
other side. For a nonzero factor, multiplication by its existing guarded
inverse proves cancellation. Applying cancellation to `a*b=a*zero` gives
the corresponding zero-product implication; the opposite side follows by
commutativity. The nonzero-product theorem follows by contradiction.

The generic caller uses exactly the source hypotheses. The real-field caller
checks ordinary values and the failure of cancellation with a zero factor.
Negative callers exercise those guards, the inverse domain, false values and
incorrect signatures.

All 17 focused checks pass, including 10 final-statement refusals and two
installed layouts. The checker uses the task's pinned 1.1.6-beta executable.
