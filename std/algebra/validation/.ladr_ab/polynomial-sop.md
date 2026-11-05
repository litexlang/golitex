# Polynomial function interfaces

Status: authoring, 2026-10-31. Selected scope: LADR 2.10–2.12 and actual
coefficient-uniqueness dependencies, followed later by complete FTA.

The source scalar domain is R or C with its standard arithmetic. A polynomial
is an actual function on that domain admitting a finite coefficient witness.
Use native nonnegative powers and finite_set_sum, whose real and complex
closure probes have passed in Session 80553. Coefficients are finite_seq(K,n+1),
entry k+1 is the coefficient of power k, and n=0 includes constants and zero.
A degree bound on a representation is not a proof of exact degree. Coefficient
uniqueness must precede function degree; finite-field evaluation injectivity is
not assumed. The zero polynomial's source degree is minus infinity, not zero
or a negative integer substituted into native arithmetic.

A unified subset-of-C carrier probe failed at composition of function-return
membership inside lambda WD, even with an explicit coefficient-entry theorem.
Use distinct real_polynomial_value and complex_polynomial_value operations
with fixed standard-carrier contracts, as the source uses R/C. Preserve the
failed generic reproduction in the journal; do not modify the verifier. Work in the existing live
Session, record each candidate, and retain accepted context after normal
failures. Save a contiguous prefix at a coherent checkpoint, then check canonical
source and an independent imported consumer. Include trailing-zero equivalent
representations, zero, R/C examples, and false identity/carrier refusals.
No native, AST, Env/Runtime or compiler changes are authorized.

The fresh canonical 23-statement checkpoint passed after correcting two complex
prototype coefficient binders. Root Session 54118 extends that prefix. The
nonreal imported constructor with coefficients 1+i and 2+i gives p(2)=5+3i;
the final independent saved-file gate is still pending. Typed polynomial-set
members need an explicit function-carrier theorem before callable use.

Harness rule: do not submit another statement until the prior Normal envelope
is complete, and match the returned statement to the submitted candidate before
attributing success. The PR015/PU015–17 transition needs explicit recovery of
response attribution before its source prefix or consumer is accepted.

Accepted initial interface checkpoint: 36 canonical and 31 imported statements;
three expected refusals retain the nonreal value fact in one live Session.
The frozen source/executable hashes agree across check_polynomials.py. This
acceptance excludes polynomial-space closure, coefficient uniqueness, degree
and FTA; no additional numbered LADR item is marked complete by this receipt.

Next increment: same-bound evaluation add/scale laws. Reuse native finite-sum
linearity through a checked local theorem over abstract C-valued functions,
then instantiate the actual monomial terms. Publish the coefficient and power
C-membership facts before arithmetic congruence. No new folding or polynomial
normalization is introduced. General sum closure still needs zero padding of
different finite coefficient bounds.
