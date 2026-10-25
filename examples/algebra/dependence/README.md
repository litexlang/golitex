# Arbitrary finite dependence

Import `Algebra = algebra` through `[import std]`. The main consumer constructs
the real scalar field and vector space, checks the trace 0,1,3,0 for coefficients
(1,1,-1) and vectors (1,2,3), and obtains a prefix witness from the imported
general dependence lemma. It does not claim which index the existential chooses.

`contracts.lit` exercises all six interfaces over arbitrary supplied fields
and vector spaces. `boundaries/main.lit` independently checks empty-list
independence, dependence of the singleton zero vector, and nonzero scalar solving.
All maintained sources exclude trust and axioms.

Run `python3 examples/algebra/dependence/check.py` after a release build.
The checker verifies strict positives, nine controls where only the final
statement may reject, archive/shared-data imports, and std/WiX inventory equality.
Controls cover the old length-two bound, missing dependence, zero/empty
coefficients, zero scalar, empty dependence, invalid index, missing zero tail,
and missing pointwise prefix agreement.

This is a prerequisite for exchange and dimension theory. It does not establish
basis exchange, basis existence, span-preserving removal, or dimension invariance.
