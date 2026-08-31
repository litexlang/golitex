# Litex → Lean, with a Property-Centered Companion

This showcase now explains two related ideas without blurring their ownership:

1. `main.lit` is the production Litex → generated Lean pipeline for
   `1 + 3 + ⋯ + (2n - 1) = n²`.
2. `property_flow.lit` shows the fuller mathematical lifecycle the source
   language should encourage: define a `prop`, prove a reusable law about it,
   prove an instance, and compose those results into a new conclusion.

## Artifact ownership

| File | Owner and role |
| --- | --- |
| `main.lit` | production mathematical source verified by Litex and translated by ToLean |
| `property_flow.lit` | Litex-verified companion for the complete property lifecycle |
| `LitexToMathlibPipelineGenerated.lean` | generated translation of `main.lit`; never hand-edited |
| `LitexToMathlibPipelineAdapter.lean` | external-AI native Mathlib adapter; not compiler output |
| `LitexToMathlibPipelineDownstream.lean` | ordinary Mathlib consumer of the adapter |

The executable ownership flow is:

```text
main.lit
   ↓ Litex verification and ToLean translation
LitexToMathlibPipelineGenerated.lean
   └─ source-owned declarations only

property_flow.lit
   ↓ Litex verification
prop definition → reusable law → odd-sum instance → nonnegative conclusion

external AI reads both mathematical contexts
   ↓ writes a separate native Lean mirror
LitexToMathlibPipelineAdapter.lean
   ↓ imported by
LitexToMathlibPipelineDownstream.lean
```

The generated module contains the canonical `Litex.Same` theorems
`__Compiler_main.sum_first_odds` and
`__Compiler_main.sum_first_ten_odds`. It contains no `namespace Native`,
private native certificate, Mathlib corollary, or consumer.

## The property flow

The companion source defines a relation with a supplied witness:

```litex
prop is_square_of(value, root Z):
    value = root^2
```

This is a `prop`, not a function: callers provide `value` and `root`, and the
relation says whether they fit. It is also intentionally not yet the
existential property “there exists some root”; retaining the witness makes the
constructor and consumer interfaces visible.

The reusable consumer is:

```litex
thm square_of_is_nonnegative:
    ? forall value, root Z:
        $is_square_of(value, root)
        =>:
            value >= 0
    root^2 >= 0
```

The source then packages the established odd-sum equality as a property fact:

```litex
thm sum_first_odds_is_square_of_n:
    ? forall n Z:
        n >= 1
        =>:
            $is_square_of(sum(1, n, kth_odd), n)
    by thm sum_first_odds(n) => sum(1, n, kth_odd) = n^2
    by def $is_square_of(sum(1, n, kth_odd), n)
```

Finally it composes the constructor and consumer:

```litex
thm sum_first_odds_nonnegative:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) >= 0
    by thm sum_first_odds_is_square_of_n(n) => $is_square_of(sum(1, n, kth_odd), n)
    by thm square_of_is_nonnegative(sum(1, n, kth_odd), n) => sum(1, n, kth_odd) >= 0
```

Those two explicit calls are reader bridges: one constructs the property and
one consumes its general law. Liveness probes show that either call can be
inferred after the other is made explicit, but the bodyless theorem fails; the
two-line form best exposes the intended architecture.

## Generated and native sides

ToLean currently translates `main.lit` only. The native adapter separately
defines `ExternalAI.IsSquareOf`, proves `square_of_is_nonnegative`, packages
the native odd-sum result, and derives nonnegativity. This mirrors the
mathematics but does not falsely claim that the adapter was synthesized from
the companion source.

The current production compiler fails closed on the companion's named local
predicate consumers. In particular, it does not yet consume the local
`by thm`/`by def` steps in `sum_first_odds_is_square_of_n`, or the
predicate-projected equality used by `square_of_is_nonnegative`. A stronger
existential wrapper such as

```litex
prop is_integer_square(value Z):
    exist root Z st {value = root^2}
```

is already Litex-verifiable, but its predicate-backed local `obtain` is one
more compiler consumer still required. These are compiler Result-consumer
gaps, not unproved mathematics.

## Suggested next examples

1. Make `property_flow.lit` a second generated module after adding named
   predicate-premise, `by thm`, `by def`, and local `obtain` consumers. This is
   the highest-value next pipeline example because it completes the exact
   prop lifecycle above.
2. Generalize `is_square_of(value, root)` to existential
   `is_integer_square(value)`, then prove closure under multiplication and
   nonnegativity. This tests witness introduction and elimination rather than
   only equality transport.
3. Add a set property example modeled after
   `lean/examples/50_SetExtensionResultComposition.lit`: define a membership
   property, prove two inclusions, then conclude set equality.
4. Add a finite classification example modeled after
   `lean/examples/51_FiniteEnumerationResultComposition.lit`: define a finite
   admissibility prop, prove candidates belong, then derive an exhaustive
   conclusion.

## Reproduce it

From the repository root:

```bash
cargo build --release
target/release/litex -compact -strict -graph -isolated \
  -f showcases/litex_to_lean_mathlib_pipeline/main.lit
target/release/litex -compact -strict -graph -isolated \
  -f showcases/litex_to_lean_mathlib_pipeline/property_flow.lit
target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/main.lit \
  showcases/litex_to_lean_mathlib_pipeline/LitexToMathlibPipelineGenerated.lean
cargo test --release --test stmt_result_to_lean_compiler_tracers \
  litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted
cd lean
lake build LitexToMathlibPipeline
```

Both Litex runners must exit `0` with top-level `ok: true`; the drift test must
reproduce the checked-in generated file; and Lake must accept the generated,
adapter, and downstream layers as visibly separate artifacts.
