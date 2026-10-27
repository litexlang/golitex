# Natural binomial coefficients

The std function binomial_coefficient(n,k) takes two natural indices and returns
a natural number. This imported caller checks B(5,2)=B(5,3)=10, the full
positive-column Pascal relation, low-column formulas, diagonal and penultimate
entries, positivity, and weak/strict row order. Row0, column0, above-row zeroes
and the new diagonal in the next row are included.

Begin with `release obj def comb::main::binomial_coefficient`. This uses the
existing explicit definition-release contract, so the caller can check both
function applications and theorem conclusions. It adds no wrapper or premise.

Run `python3 examples/combinatorics/binomial/check.py`. The checker verifies
strict source,39 concrete statements,14 independent generic statements and a
six-statement README excerpt.21 final-only controls cover natural domains,
arity, values, missing hypotheses and omitted definition release. Both actual
installed layouts and complete std/WiX payload equality are also checked.

No factorial formula, row-sum/binomial theorem or cardinality of k-subsets is
established here. The recursive natural function and its checked laws are the
current interface. No Rust/kernel, Lean or global release change is claimed.
