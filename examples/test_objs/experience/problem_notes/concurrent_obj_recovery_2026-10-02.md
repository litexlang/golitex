# Unchanged Obj fixtures recovered during concurrent work

Task: numeric and aggregate repair; scope here is final corpus synchronization.
The final whole-corpus gate also observed 24 unrelated former gaps now meeting their
intended result. Their original sources and exact observations are retained in
[the journal](../../proof_journals/numeric_aggregate_concurrent_promotions_2026-10-02.json).
Four rejection controls remain negatives and 20 positive cases moved to their owning
files. This task did not implement those unrelated engine changes.

Reusable lesson: preserve the original statement, rerun with stable current source and
binary, then promote only the observed result. A known-gap baseline cannot certify repairs.

The former Normal-output WD diagnostic limitation also recovered: the unchanged
`sqrt(-1) = sqrt(-1)` control still rejects, and Normal JSON now retains
`ExpLogOperator/Sqrt/requirement`, `sqrt (-1)` and the failed `0 <= -1` fact.
The final verification journal preserves this separate diagnostic observation;
it is outside the numbered fixture inventory.
