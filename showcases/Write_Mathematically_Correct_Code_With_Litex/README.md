# Write Mathematically Correct Code With Litex

Created and maintained by Jiachen Shen

> Executable code can be an exported view of verified mathematics, rather
> than a second implementation that must be kept synchronized with it.

## The insight: single-source verified computation

A proof can be correct while production code implements something slightly
different. The problem is structural: specification, proof model, and program
often have separate semantic owners, so the final implementation can drift.

Litex tests a different architecture. Define the mathematical function once,
use that exact definition in theorems, attach its exhaustive executable cases,
and extract those cases into an ordinary language:

```text
one Litex definition
    ├── mathematical properties and proofs
    └── checked executable cases → Python or C
```

This is more than code generation. The theorem and the emitted program share
the same source definition. Changing the algorithm therefore changes the
mathematical object whose properties must be checked; there is no second
formula to update after the proof.

## Newton's method is only the tracer

Here, `newton_sqrt_two_step` is both the transition used by the verified
trajectory in [`main.lit`](main.lit) and the function exported to
[`newton_sqrt_two.py`](newton_sqrt_two.py). Litex proves the concrete exact
residual after two steps from `1`:

```text
x0 = 1,  x1 = 3/2,  x2 = 17/12
|x2^2 - 2| = 1/144 <= 1/64
```

Newton's method is replaceable; **one semantic owner for specification, proof,
and executable behavior** is the reusable technique. The detailed mathematical
model belongs in [`math_collections.md`](math_collections.md), not in this
overview.

## Run

```bash
target/release/litex -r showcases/Write_Mathematically_Correct_Code_With_Litex
target/release/litex -extractpython -f showcases/Write_Mathematically_Correct_Code_With_Litex/main.lit
target/release/litex -extractc -f showcases/Write_Mathematically_Correct_Code_With_Litex/main.lit
```

The `# [-extract]` block is verified and emitted as `newton_sqrt_two_step`. The
surrounding proof stays in ordinary full-file verification and is not sent to
Python or C.

## Why this matters

The whole application does not need to become a formal program. A small,
mathematically critical kernel can live in Litex, while ordinary Python or C
owns orchestration, I/O, libraries, and deployment. Verified mathematics can
then enter existing software as a component instead of as a document that must
be manually reimplemented.

## Boundary

The proof uses exact real arithmetic; generated Python and C use target-language
numeric semantics. This showcase establishes a shared source for the formula,
branches, a concrete trajectory, and an exact-real residual bound. It does not
establish IEEE-754 rounding, overflow, compiler correctness, or correctness of
the surrounding application.

The Litex source contains no `trust` or project axiom. Its checking boundary
still includes the Litex parser, verifier, builtin rules, inference rules, and
extractor. This is one supported instance of the architecture, not a general
theorem about all extracted programs.

> **Source shape note:** the file uses concrete unrolling instead of
> `have fn … R by induc` and instead of nested `forall n` + `by induc n`, both
> of which are blocked on the current kernel without a kernel change.
