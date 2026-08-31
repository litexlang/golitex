# School Mathematics in a Nutshell

This standalone showcase is the short companion to the mathematical map in
`scripts/high_school_book/textbook/Introduction.lit`. It covers all eleven
directions in that Introduction in one linear, runnable `main.lit`:

1. sets and logic;
2. algebra, including powers and logarithms;
3. functions;
4. trigonometry;
5. plane vectors and analytic geometry;
6. complex numbers;
7. solid geometry and measurement;
8. probability;
9. statistics and data analysis;
10. sequences, induction, and combinatorics; and
11. derivatives and elementary calculus.

Each direction keeps its reusable definitions and a small concrete application
together. This makes the file read as one survey while still showing what each
interface can do.
Representative scenes include AM-GM for `9` and `16`, a cosine-law recovery of
the 3-4-5 triangle, a circle and ellipse as coordinate point sets, the modulus
of `3+4i`, a rectangular-prism volume, fair-die and Bayes calculations, a
three-point regression slope, factorial counting, induction on `2^n`, and the
constant difference quotient of a circumference function.

The module uses native numeric carriers, Cartesian products, finite sets,
trigonometric and complex operations, factorial, and square root. It contains
no direct `trust`, local axiom, or import from the larger high-school book; the
book guides the domain selection, while this module remains independently
runnable. The set layer also exposes and immediately applies
`symmetric_difference` as a real-valued set construction.

Run it from the repository root with:

```bash
target/release/litex -compact -graph -r showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell
```

`same_math_in_lean.lean` is a selected comparison rather than a line-for-line
mirror of the expanded survey. It checks the original arithmetic, equations,
AM-GM, functions, sequences, coordinate distance, fair-die probability, and
basic statistics scenes in Mathlib.
