# Middle-School Mathematics in a Nutshell

This independent showcase follows one compact mathematical mainline rather
than splitting the curriculum into branches. Its classic examples are:

- the native calculation `gcd(84,30)=6`;
- linear isolation and the roots of a factorized quadratic;
- two-variable AM-GM, evaluated at `9` and `16`;
- a linear function and the constant difference of an arithmetic sequence;
- the 3-4-5 triangle as a coordinate-distance calculation; and
- a fair-die probability followed by the mean and range of `2,4,6`.

The selection is informed by `scripts/high_school_book/textbook/`, but this
module remains standalone and intentionally small. Run it from the repository
root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell
```

`main.lit` uses native numeric carriers, `gcd`, Cartesian products, finite
sets, square root, and finite-set size. It contains no direct `trust` or local
axiom and does not recreate those builtin concepts through local wrappers.

`same_math_in_lean.lean` expresses the same mainline with only Lean's
automatically loaded Prelude. Where Prelude lacks real square root or rational
probability, the exact required boundary is explicit rather than attributed to
Mathlib or to the Litex-to-Lean compiler. Run it with:

```sh
lean showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/same_math_in_lean.lean
```
