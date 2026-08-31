# From readable Litex mathematics to a native Lean theorem

This example proves that the sum of the first `n` positive odd integers is
`n²`. The proof is written in Litex, compiled to checked Lean evidence, and
then exposed as an ordinary Mathlib theorem.

```text
main.lit  ->  Generated.lean  ->  Adapter.lean  ->  Final.lean
readable      compiler-owned      small interface    native theorem
proof         proof evidence      to Mathlib         statement
```

## Why write Litex and then Lean?

Litex performs the mathematical verification. In this example, the
handwritten Lean work does not repeat the induction proof: it only states the
clear correspondence between the generated Litex objects and their Lean
counterparts. That interface is short because the integer sum, odd-number
function, and equality represented by Litex have explicit Lean meanings.
Thus the formalization cost after writing the Litex proof is reduced to a
small representation adapter rather than a second proof.

Litex is also designed to remain close to readable mathematical argument.
Its source is easier to inspect and generate than proof-assistant internals,
which lowers the entry barrier for non-specialists and makes the same proof
artifact practical for both humans and AI to read and edit. Lean remains the
independent kernel checker and the final Mathlib-facing language.

## The proof boundary

`main.lit` contains the induction:

```litex
thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ...
```

`Generated.lean` is exact compiler output. `Adapter.lean` cites its
`__Compiler_main.sum_first_odds` theorem and converts the checked numeric
representation to a native `Finset.Icc` sum. It does not prove the identity
again.

`Final.lean` then states the desired theorem without any Litex vocabulary:

```lean
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact Adapter.sumFirstOddsNative 100 (by norm_num)
```

The statement deliberately knows nothing about Litex. Only its proof body
uses the handwritten adapter.

## Run the example

Prerequisites are Rust/Cargo and Elan. From the repository root:

```bash
cargo build --release
target/release/litex -strict -f \
  showcases/litex_to_lean_mathlib_pipeline/showcase1/main.lit
```

Generate Lean from this exact `main.lit` and compare it with the checked-in
artifact:

```bash
target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/showcase1/main.lit \
  /tmp/showcase1.Generated.lean

cmp /tmp/showcase1.Generated.lean \
  showcases/litex_to_lean_mathlib_pipeline/showcase1/Generated.lean
```

`cmp` exits successfully only when the files are byte-identical. To check the
Lean side:

```bash
cd showcases/litex_to_lean_mathlib_pipeline/showcase1
lake build
```

The first Lake build may download the pinned Lean/Mathlib dependencies.

## Files

| File | Ownership |
| --- | --- |
| `main.lit` | Handwritten mathematical proof |
| `Generated.lean` | Compiler output; do not edit |
| `Adapter.lean` | Handwritten Litex-to-Mathlib interface |
| `Final.lean` | Native Lean theorem and proof consumer |
| `litex.config` | Litex module registration |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Reproducible Lean project |

This showcase establishes the complete path for the numeric objects used
here. It does not claim that every Litex object already has a native Mathlib
adapter. The checked path contains no `axiom`, `sorry`, or `admit`.
