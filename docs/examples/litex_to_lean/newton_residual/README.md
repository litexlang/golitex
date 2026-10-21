# Newton single-step identity: a checked compiler example

This example defines a function on nonzero real inputs and proves one exact
algebraic identity. It shows how the source domain condition survives generated
function calls and the handwritten adapter. For the smaller representation
conversion alone, start with [adding zero](../add_zero/README.md).

The recursive residual-bound example also has a generated proof checked by
Lean as of 2026-10-21. Its ordinary Mathlib interface remains unfinished.

## Litex input

The complete [source](../../../../lean/examples/newton_residual_identity/statement.lit) is:

```litex
# Newton's exact algebraic error identity for a nonzero real input.
have fn newton(x R:x!=0) R=(x+2/x)/2
forall x R:
    x!=0
    =>:
        newton(x)^2-2=((x-2/x)/2)^2
```

## Generated Lean and ordinary Lean use

The paired [statement.lean](../../../../lean/examples/newton_residual_identity/statement.lean)
is actual compiler output. It imports [Litex.lean](../../../../lean/Litex.lean)
and contains the function object `_object_i1`, its function-space membership
`h_357`, and the universal identity `h_361`. The input stays a generic
`Litex.Obj`; real membership `h_374` and nonzero fact `h_359` are explicit
certificates used by the function call and division constructors.

[Adapter.lean](Adapter.lean) instantiates the numeric model and translates the
generated identity into ordinary real arithmetic. Its proof uses `h_361`,
function evaluation and operation denotation laws. It does not independently
reprove the algebraic identity.

The complete handwritten [Final.lean](Final.lean) is the ordinary Lean consumer:

```lean
import newton_residual.Adapter

theorem newtonResidualIdentity (x : ℝ) (hx : x ≠ 0) :
    ((x + 2 / x) / 2)^2 - 2 = ((x - 2 / x) / 2)^2 := by
  exact Adapter.newtonResidualIdentity x hx
```

The source and generated file have passed strict Litex verification, actual
compilation and byte-for-byte regeneration. The generated module, Adapter and
Final have passed Lean 4.31.0 with Mathlib revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The native theorem has a live
proof dependency on the generated `h_361`; a discarded citation is rejected by
the dependency control. The axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`.

To regenerate the paired file with the release CLI, run from the repository root:

```bash
target/release/litex -strict -lean -f lean/examples/newton_residual_identity/statement.lit
```

This command writes Lean to stdout. The generated file and handwritten adapter
are separate artifacts; the short native theorem above is not the raw output
of `-lean`. The [compiler README](../../../../src/compile_to_lean/README.md)
explains the architecture, while the [compiler guide](../../../Litex_To_Lean_Compiler_Guide.md)
explains its user-facing workflow.

## Another checked example

The [positive-update source](../../../../lean/examples/newton_positive_update/statement.lit)
and [generated Lean](../../../../lean/examples/newton_positive_update/statement.lean)
also have a checked [PositiveAdapter](PositiveAdapter.lean) and
[PositiveFinal](PositiveFinal.lean). They export
`newtonPositive (x : ℝ) (hx : 0 < x) : 0 < (x + 2 / x) / 2` and exercise
`claim`, a positive input domain and a positive return constraint.

## Recursive residual bound

The larger [source](../../../../lean/examples/newton_residual_bound/statement.lit)
targets `|x_n^2 - 2| ≤ 4*(1/4)^(2^n)` for the recurrence
`x_0 = 1`, `x_(n+1) = (x_n + 2/x_n)/2`. On 2026-10-21, strict compilation and
full generated Lean checking succeeded after constructor sharing and numerical
observation fixes. The output is 1,580,059 bytes, down from 7,341,525 bytes.
The check used Lean 4.31.0 and `maxHeartbeats = 2000000`, above Lean's default
200000 budget.

The native all-index interface remains unfinished. This check establishes the
generated Litex theorem, with its explicit semantic parameters. Development
notes and receipts remain in the local-only `scripts/litex_to_lean/` workspace.
