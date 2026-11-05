# Polynomial coefficient laws

Import this module as `Polynomials = polynomials` under `[import std]`.
It consumes the existing real and complex polynomial functions in
Algebra::polynomial and the native complex sum proofs in ComplexSums.
It does not replace polynomial functions with coefficient records.

The public `coefficients` export contains matching real and complex theorems:

| Interface suffix | Contract |
| --- | --- |
| polynomial_coefficients_unique | Equal polynomial functions with exponent bounds n and m have equal coefficients at every common position |
| polynomial_excess_coefficients_zero | Coefficients beyond the shorter representation are zero |
| polynomial_coefficient_vector_unique | With one fixed exponent bound, equality of polynomial functions implies equality of the complete coefficient vectors |
| polynomial_leading_bounds_unique | When both last coefficients are nonzero, equal polynomial functions have equal exponent bounds |

Each name has a `real_` or `complex_` prefix and one fixed scalar contract.
Coefficient entry k+1 represents exponent k. Bounds n,m are natural, including
zero; trailing zeros are permitted except in the leading-bound theorem, which
explicitly requires both last coefficients nonzero. Comparing vectors with
different lengths produces entry and zero-tail facts, not raw vector equality.

The proofs explicitly restrict the original R->R or C->C functions to R+->C.
Real coefficient vectors are copied entrywise into C, and finite-sum substitution
checks the embedding. Typed function aliases expose the supplied whole-function
equality before congruence is applied to values. The source adds no axiom,
trust, builtin rule, parser, verifier or compiler change.

The strict source gate passes 9 statements. The independent imported file
passes 37 statements, including nonreal constant i and real constant -3 with
bounds 0 and 3, proved equal as functions on their complete original domains.
Six refusals reject zero leading terms, an invalid common index and missing
whole-function equality, each for R and C while preserving valid context.
The separate clean boundary replay also passes.
See [source receipt](validation/.ladr/source_gate.json),
[imported receipt](validation/.ladr/use/imported_gate.json) and
[checker](validation/.ladr/check_coefficients.py). The per-increment
[checker](validation/.ladr/check_coefficients.py) records the source
snapshot before the following degree exports were registered.

## Exact degree

The registered truncation, finite_degree and bounded_degree exports contain
5, 13 and 6 source statements. The 21-statement degree_value export proves
existence and uniqueness of a degree value for every polynomial: a natural
degree for nonzero functions, or the existing negative-infinity object for zero.
The 33-statement degree export constructs the real and complex selectors from
that unique specification. This degree checkpoint contains 87 source statements;
the membership export below brings the registered module to 94.

The functions real_polynomial_degree and complex_polynomial_degree take the
original functions with the existing is_real_polynomial / is_complex_polynomial
predicate in their strict input domain. They return degree_value::PolynomialDegree,
exactly union(N,{Extended::main::real_negative_infinity}). Release the selected
function's recorded interfaces before imported use:

```litex
release obj def Polynomials::degree::complex_polynomial_degree
```

After proving the original polynomial predicate for p,
complex_polynomial_degree_domain(p) publishes its selector-domain membership.
The real interface has the corresponding real prefix. The zero theorem returns
negative infinity; nonzero_carrier and nonzero_specification expose the natural
degree and its nonzero-leading-coefficient representation. The
agrees_with_finite_degree theorem computes the value from any such representation.

The real_polynomial_degree_at_most and complex_polynomial_degree_at_most
predicates use the existing extended-real order. The theorems
polynomial_degree_at_most_of_bounded and polynomial_bounded_of_degree_at_most,
with the appropriate scalar prefix, prove both directions for the existing
Algebra::polynomial bounded monomial spans. Zero belongs to every natural bound.

The [degree check](validation/.ladr/check_degree.py) passes the 33-statement
source target with its 54 registered predecessors, 163 independent imported
statements and ten retained-context refusals. Examples include degree-2 real
and complex quadratics, nonzero constants represented through bound 3, zero,
and bounds 0/2/5/7. Refusals cover false degrees, too-small bounds, confusing
representation bounds with exact degree, a natural degree for zero and inputs
without polynomial evidence. See [checker](validation/.ladr/check_degree.py).

No axiom, trust, new native mathematical operation or kernel change is introduced.
LADR 2.11 and 2.12 are accepted. General root count and complete fundamental
theorem of algebra remain unfinished.

## Original polynomial-set inputs

The membership export proves real_polynomial_definition_membership and
complex_polynomial_definition_membership for inputs in the original named
Algebra polynomial sets. These publish the exact strict selector domain.
The matching polynomial_membership_specification theorems expose the original
function carrier and polynomial predicate. The proof uses a general source
theorem transferring membership across equal sets; it adds no verifier branch.

The [membership check](validation/.ladr/check_membership.py) passes seven source
statements with 87 registered predecessors, 28 independent imported statements
and four retained-context refusals. It calls degree directly on values declared
in the original named polynomial sets, including -3 and i, and checks the generic
zero specification. The refusals reject original-function inputs lacking the
required polynomial-set or selector-domain evidence. See the
[checker](validation/.ladr/check_membership.py).

