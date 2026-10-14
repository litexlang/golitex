# Adding zero: from Litex to ordinary Lean

This elementary example follows one checked fact through the compiler and a
handwritten adapter. It shows that a source complex member remains a generic
certified object in generated Lean; obtaining an ordinary `x : ℂ` theorem is
a separate representation conversion that consumes the generated proof.

## Litex source and generated proof

The complete [source](../../../../lean/examples/add_zero/statement.lit) is:

```litex
# Adding zero leaves every complex object unchanged.

forall a C:
    a + 0 = a
```

From the repository root,
`litex -strict -lean -f lean/examples/add_zero/statement.lit` writes Lean source
to stdout. The paired [generated file](../../../../lean/examples/add_zero/statement.lean)
contains that output and imports [Litex.lean](../../../../lean/Litex.lean).

Its theorem `h_2` says that a complex member plus zero is `Litex.Same` to the
original object. The input remains a generic `Litex.Obj` with a separate
membership fact `h_15`; the addition constructor receives membership proofs
for both operands. The compiler replays the checked source result, including
these construction conditions.

## Adapter

The complete handwritten [Adapter.lean](Adapter.lean) is:

```lean
import examples.add_zero.statement

namespace Adapter

theorem complexAddZero (x : ℂ) : x + 0 = x := by
  let M := Litex.NumericModel.model
  have h := LitexCompiled.file_lean_x2f_examples_x2f_add_x5f_zero_x2f_statement_x2e_lit.h_2
    (M := M) (Litex.number x) (Litex.numberInC x)
  exact (Litex.NativeBridge.addSame_iff x 0 x).mp h

end Adapter
```

`M` selects the concrete numeric model. `Litex.number x` represents the native
complex number, and `Litex.numberInC x` supplies its membership certificate.
The adapter calls the generated `h_2`; the proved `addSame_iff` bridge converts
that result into native `x + 0 = x`. It does not prove the identity again.

## Ordinary Lean consumer

The complete [Final.lean](Final.lean) is:

```lean
import add_zero.Adapter

theorem complexAddZero (x : ℂ) : x + 0 = x := by
  exact Adapter.complexAddZero x
```

Its theorem statement uses only Mathlib's `ℂ`, addition and equality. Only the
proof body calls `Adapter`. The artifact chain is:

```text
statement.lit → statement.lean → Adapter.lean → Final.lean
                 generated       handwritten    ordinary Lean interface
```

The short Final is a consumer of the compiled proof, not the raw compiler
output. Source/generated pairs belong under `lean/examples/`; the handwritten
adapter and consumer for this example belong beside this README under
`docs/examples/litex_to_lean/`.

## Checked scope and navigation

On 2026-10-14, this source regenerated the same Lean bytes, and the generated
module, Adapter and Final passed Lean 4.31.0 with the pinned Mathlib environment.
The proof dependency check confirmed that Final reaches the generated `h_2`
through Adapter; the axiom audit found only standard Lean axioms. These are
checks of this example, not a claim of complete compiler coverage or automatic
native interface generation.

The [compiler README](../../../../src/compile_to_lean/README.md) explains the
architecture and layer contracts. The [compiler guide](../../../Litex_To_Lean_Compiler_Guide.md)
explains the [native workflow](../../../Litex_To_Lean_Compiler_Guide.md#using-a-generated-result-in-ordinary-mathlib)
and [acceptance boundary](../../../Litex_To_Lean_Compiler_Guide.md#what-successful-output-establishes).
[CLI documentation](../../../cli.md#lean-compiler-boundary) owns invocation and
output behavior. For a preserved function domain condition, continue with the
[checked single-step Newton example](../newton_residual/README.md).
