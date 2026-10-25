# Euclidean transformations and supplied modular inverses

The imported 49-statement caller checks the 84/30 Euclidean chain, negative
integers, a zero first gcd operand, a supplied Bezout identity and scaled
integer solutions. For 5 modulo 12, Bezout supplies inverse 5; cancellation and
linear congruence solution/uniqueness follow. Inverse17 is congruent to5, so
uniqueness is modulo 12. The modulus 1 case permits zero coefficients.

The caller also proves that every integer u fails to invert2 modulo 6, while
2*1 and 2*4 are congruent modulo 6 but 1 and 4 are not. The library never asserts
general Bezout or inverse existence. contracts/main.lit independently calls
all 10 new theorem signatures, with no concrete prefix. readme/main.lit is
the second std README excerpt. 20 negative projects must accept their setup
and reject only their final statement at negative/expected.json's phase.

```bash
python3 examples/number_theory/euclidean_inverses/check.py
```

The checker verifies strict source/callers/contracts/README, both actual
archive/shared-data installed imports and full std/WiX payload/component
agreement. The older congruences project remains a separate regression.
No Lean or repository-wide release certification is implied.
