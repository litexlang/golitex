# Litex → Lean, Then an External Mathlib Adapter

This showcase fixes a strict ownership boundary around the theorem

```text
1 + 3 + 5 + ⋯ + (2n - 1) = n²,  for every integer n ≥ 1.
```

ToLean translates the `.lit` declarations and their verified proof routes. It
does not invent a second theorem merely because a native Mathlib signature
would be convenient. Any such interface is a separate artifact authored by an
external AI or human.

## Artifact ownership

| File | Owner and role |
| --- | --- |
| `main.lit` | mathematical source verified by Litex |
| `LitexToMathlibPipelineGenerated.lean` | generated ToLean translation; never hand-edited |
| `LitexToMathlibPipelineAdapter.lean` | external-AI Lean adapter; not compiler output |
| `LitexToMathlibPipelineDownstream.lean` | ordinary Mathlib consumer of the adapter |

The flow is deliberately explicit:

```text
main.lit
   ↓ Litex verification and ToLean translation
LitexToMathlibPipelineGenerated.lean
   └─ source-owned declarations only

external AI reads the mathematical/generated context
   ↓ writes a separate Lean module
LitexToMathlibPipelineAdapter.lean
   ↓ imported by
LitexToMathlibPipelineDownstream.lean
```

The generated module contains the canonical `Litex.Same` theorems
`__Compiler_main.sum_first_odds` and
`__Compiler_main.sum_first_ten_odds`. It contains no `namespace Native`,
private native certificate, Mathlib corollary, or consumer.

The adapter exposes the independent native theorem

```lean
theorem LitexToMathlibPipeline.ExternalAI.sum_first_odds
    (n : ℤ) (one_le_n : 1 ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2
```

Its Lean proof is owned by that adapter. Importing the generated module gives
the external author context; it does not falsely claim that ToLean synthesized
or derived this new public statement.

## The Litex proof

Both induction cases contain their calculations directly. The base is:

```litex
? from n = 1:
    kth_odd(1) = 2 * 1 - 1 = 1
    sum(1, 1, kth_odd) = kth_odd(1) = 2 * 1 - 1 = 1 = 1^2
```

There is no one-use singleton, sum-step, or square-step theorem and no explicit
theorem invocation. The verifier retains checked function reduction,
registered integer-sum rules, the exact induction-hypothesis `FactId`, and
arithmetic normalization. ToLean replays that evidence only for the source
declarations.

The source then specializes its own universal result without `by thm`:

```litex
thm sum_first_ten_odds:
    ? forall:
        sum(1, 10, kth_odd) = 100
    sum(1, 10, kth_odd) = 10^2 = 100
```

Ordinary known-`forall` matching selects `sum_first_odds(10)` for the first
edge, and checked numeric normalization closes `10^2 = 100`. The generated
Lean theorem cites the generated universal theorem directly.

## Reproduce it

From the repository root:

```bash
cargo build --release
target/release/litex -compact -strict -runner -isolated \
  -f showcases/litex_to_lean_mathlib_pipeline/main.lit
target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/main.lit \
  showcases/litex_to_lean_mathlib_pipeline/LitexToMathlibPipelineGenerated.lean
cargo test --release --test stmt_result_to_lean_compiler_tracers \
  litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted
cd lean
lake build LitexToMathlibPipeline
```

The Litex runner must exit `0` with top-level `ok: true`; the drift test must
reproduce the checked-in generated file; and Lake must accept the generated
translation, external adapter, and downstream consumer as three visibly
separate layers.
