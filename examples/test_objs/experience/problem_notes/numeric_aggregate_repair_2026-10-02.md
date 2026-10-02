# Exact numbers and aggregate repairs

Task: implement the four approved stages of the Obj corpus numeric/aggregate plan.
Scope: Number construction and persistence, imaginary nonzero and guarded complex equality,
finite aggregate evaluation/equality, symbolic rules and aggregate domain checking.

The unchanged reproductions closed 15 issues: decimal equality/false inequality, complex
inverse, range sum/product values, finite-set values and two incorrectly admitted domains.
All seven selected object files, 24 negatives and 12 positive-gap fixtures passed their
intended gate before promotion. The exact original sources, diagnostics, source and binary
hashes are preserved in [the promotion journal](../../proof_journals/numeric_aggregate_promotions_2026-10-02.json).
The 12 positive fixtures now live in their owning positive files; three repaired negatives
remain executable rejection controls. Earlier baseline reports are historical.

Use exact Number normalization at every construction/decoder entrance. Imaginary nonzero is
a dedicated builtin; division still checks each denominator. Aggregates check source WD,
instantiate by binding identity and fold exact terms under a shared finite allowance.
Symbolic identities retain their mathematical premises. `eval` displays a result without
publishing an equation; direct equalities own their checked publication.

Gate: `python3 examples/test_objs/run.py --object number --object imaginary_unit --object div
--object sum --object product --object sum_of_finite_set --object product_of_finite_set`.
Final broadened acceptance and remaining limits are recorded in [acceptance](../../acceptance.md).
