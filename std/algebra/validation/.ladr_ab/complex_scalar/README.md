# Native complex scalars: source concordance

LADR 1.1 is represented using native C, re, img and ordinary scalar arithmetic.
The check proves reconstruction, the coordinate formulas for addition and
multiplication, both coordinate projections, and a unique pair of real
coordinates for every complex scalar. It does not equate the native set C with
the Cartesian product as a literal set: the checked coordinate correspondence
provides the book's pair interpretation.

Items 1.3 and 1.5 reuse native commutative field laws, unique additive and
nonzero multiplicative inverses, subtraction and guarded division. No new
mathematical interface, native rule, axiom or trust was introduced.

The strict independent file gate accepts nine general claims with exit 0.
Three Session controls reject division by zero, an incorrect imaginary
coordinate and a false nonreal product; a valid product remains available
after every refusal. Run check.py with LITEX_CHECK_BINARY set to the current
release executable. The checker always executes these cases and uses no saved receipts.

