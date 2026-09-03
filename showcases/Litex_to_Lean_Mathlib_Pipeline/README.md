# From readable Litex mathematics to a native Lean theorem

> Litex does not need to replace Lean—or look like Lean—to end in a native
> theorem checked by Lean.

## Why this showcase exists

A formalization workflow can now be organized around two different authorship
choices:

| Lean-first workflow | Litex-assisted workflow |
| --- | --- |
| Write the mathematical statement, definitions, proof, and representation plumbing in Lean. | Write the main mathematical construction in Litex, then add a thin semantic Adapter and consume the result as native Lean. |

For Lean workers, this changes the default loop: Lean remains the final
language and kernel, but the bulk of a supported mathematical construction can
be authored first in Litex. The Adapter is not a second proof; it translates
the checked representation at the boundary so the final theorem can use
ordinary Lean/Mathlib objects.

For non-Lean workers, the shift can be larger. They can work in a compact,
fact-oriented language that stays close to mathematical argument, while a
small, explicit Adapter handles the Lean-specific representation details. For
supported proof shapes, this can make the mathematics easier to read, write,
and reuse than authoring the entire development in Lean. The claim is a
workflow hypothesis with a concrete supported example, not a promise that all
Lean proofs or all Litex objects become easier.

The Adapter is not necessary for the Litex proof itself; it is an
interoperability layer for the Lean handoff. A checked Litex development can
remain entirely in Litex, while a thin Adapter becomes valuable when its result
needs to enter Lean/Mathlib as an ordinary theorem that can use their native
library and kernel.

That is the distinctive Litex idea here: **a readable authoring layer can
cooperate with a mature checking ecosystem without becoming isolated from it**.
The example proves in Litex that the first `n` positive odd integers sum to
`n²`, compiles that proof, and then uses it to prove a native Lean theorem that
the first 100 sum to 10000.

```text
main.lit  ->  Generated.lean  ->  Adapter.lean  ->  Final.lean
```

This is one complete supported vertical slice—not a claim that every Litex
object or proof already has a Lean/Mathlib translation.

## Why the Adapter is necessary

`Generated.lean` is proof replay, not the public API a Lean mathematician
would normally write. Its theorem deliberately preserves Litex's semantic
interfaces, including `Litex.Le`, `Litex.sum`, `Litex.Same`, numeric carrier
casts, and compiler-owned names such as `__Compiler_main.sum_first_odds`.
Those wrappers make the translation explicit, but a reusable Mathlib theorem
should instead expose native order, `Finset` sums, and Lean equality.

`Adapter.lean` is the boundary between those two representations:

| Generated Litex-facing representation | Native Lean/Mathlib representation |
| --- | --- |
| `Litex.Le (1 : ℂ) (n : ℂ)` | `(1 : ℤ) ≤ n` |
| `Litex.sum 1 n kth_odd` | `∑ k ∈ Finset.Icc 1 n, (2 * k - 1)` |
| `Litex.Same ... ...` with integer/complex carrier evidence | ordinary Lean `=` |
| `__Compiler_main.sum_first_odds` | `Adapter.sumFirstOddsNative` |

The Adapter accepts a native integer and premise, converts the premise to the
generated representation, cites the generated theorem, extracts its equality
evidence through public Litex bridge lemmas, and casts the result back to the
native Mathlib statement. It does not repeat the induction or prove the odd-sum
identity a second time.

This work is therefore much shallower than reconstructing the proof in Lean.
Once the generated signature and desired native statement are fixed, writing
the Adapter is a constrained representation task: inventory the corresponding
objects, select the public bridge lemmas, and let Lean check the conversions.
That makes it suitable for coding agents such as GPT-5.6 or Claude. Their output
is not trusted: the Adapter and its native consumer must still be accepted by
the Lean kernel.

## Why To Lean matters

1. **Independent checking for supported translations.** For this supported
   path, the compiler produces a Lean proof artifact that Lean accepts. This
   gives Litex code and its verification evidence an independent, inspectable
   replay target. It strengthens confidence in the implemented path; it does
   not by itself prove that every Litex rule or future program is sound.

2. **A bridge between the Litex and Lean communities.** Once the relevant
   representations have compiler and Adapter support, a theorem proved in
   Litex can become an ordinary theorem reusable by Lean users. Litex work is
   therefore not confined to an isolated ecosystem. In the other direction,
   Mathlib's definitions, theorems, tactics, and bridge lemmas provide the
   target vocabulary that expands what Litex results can connect to.

3. **Litex as a higher-level front end to Lean.** For supported mathematical
   domains, Litex can be used to write the readable proof while Lean supplies
   the mature library ecosystem and final kernel check. Litex is particularly
   attractive for routine, short, low-abstraction “simple mathematics,” where
   the overhead of proof-assistant internals can dominate the argument itself.
   Its compact, mathematical source can be easier for both humans and AI to
   write and read, especially for non-specialists.

In this role, Litex complements Lean rather than replacing it: Litex lowers the
cost of expressing selected mathematics, and Lean remains the final
Mathlib-facing language and independent checker.

## The proof boundary

`main.lit` first records the two automatic carrier facts as anonymous
universal facts, then contains one named theorem—the general induction:

```litex
forall n Z:
    n >= 1
    =>:
        sum(1, n, kth_odd) $in Z

forall n Z:
    n^2 $in Z

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ...
```

There is no separate `n = 10` corollary. `Final.lean` instantiates this one
general theorem at `n = 100`.

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
