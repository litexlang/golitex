# Using Litex proofs in ordinary Lean

This showcase is for Lean users who want to reuse Litex proofs. A real identity
with a nonzero-denominator condition and a domain-preserving fractional-linear
involution lead from source to generated proof, representation conversion and
ordinary Lean use. Litex supplies the mathematical proof; a handwritten Adapter
converts its interface to Mathlib's real-number interface.

**This example demonstrates interoperability, without establishing a proof-length
advantage.** Mathlib already provides `add_div`; see the complete comparison in
[DirectLean.lean](DirectLean.lean). The Möbius example below also records its
working connection and direct comparison.

Start with the delivered theorem in [Final.lean](Final.lean):

```lean
theorem quotientDistributes (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact Adapter.quotientDistributes x y z hz
```

This declaration lives in the `LitexLeanExample` namespace. Its parameters,
premises and conclusion are ordinary Lean mathematical objects, so a consumer
can use the theorem in subsequent proofs.

```mermaid
flowchart LR
  S["source.lit · statement"] -->|compiler output| G["Generated.lean · proof replay"]
  G -->|handwritten conversion| A["Adapter.lean · native interface"]
  A --> F["Final.lean · ordinary theorem"]
  F -->|import Final| U["UseInYourProject.lean · downstream proof"]
```

## 1. State the mathematics in Litex

The complete [source.lit](source.lit) is:

```litex
# For a nonzero real denominator, division distributes over addition.
forall x,y,z R:
    z != 0
    =>:
        (x+y)/z=x/z+y/z
```

`x R` introduces an object and its membership in `R`. The premise `z != 0`
also establishes that division is well-defined. This example selects
`RationalWithNonzeroPremises`: rational-expression normalization under nonzero
premises. The compiler records that route in Generated; the later Adapter
converts the representation.

## 2. Understand the generated theorem's inputs

[Generated.lean](Generated.lean) is the actual compiler output and is kept
unchanged. Its exported theorem is `h_3`, in a namespace generated from the
source path. The theorem name comes from the original FactId.

The generated theorem remains generic over three host types and a mathematical
interpretation `M`. Each argument is a `Litex.Obj`, followed by an ordinary
membership fact. The source set `R` is not directly replaced by Lean's type
`ℝ`. This example supplies the arguments as follows:

| Source information | Generated signature | Value supplied by Adapter |
|---|---|---|
| Objects `x`, `y`, `z` | `_value_i1`, `_value_i2`, `_value_i3` | `a`, `b`, `c` |
| Three `R` membership facts | `h_16`, `h_17`, `h_18` | `ha`, `hb`, `hc` |
| `z != 0` | `h_1 : ¬ Litex.Same ...` | `h0` |
| Complete universal fact | `h_3` | Proof source for `generated` |

One division subterm in the generated signature looks like this, with line
breaks added for readability:

```lean
Litex.div _value_i1 _value_i3
  (Litex.realToComplex _value_i1 h_16)
  (Litex.realToComplex _value_i3 h_18)
  h_1
```

The object constructor itself receives domain and nonzero proofs. The result
of an operation remains a certified object; its equality is `Litex.Same`.
Membership, operation WD and mathematical equality retain distinct roles.

## 3. Write the Adapter: input, call, output

The public theorem in [Adapter.lean](Adapter.lean) already has the same native
statement as Final. The following three steps occur inside its proof body.

First, select a proved numeric interpretation, wrap a Lean real number, and
construct its membership fact:

```lean
let M := Litex.NumericModel.model
let a := Litex.number (M := M) (x : ℂ)
have ha := Litex.NativeBridge.numberInR (M := M) x
```

`M` fixes the objects' mathematical interpretation; this example selects the
numeric model implemented in Core. A real number is embedded into the complex
numbers and wrapped with `Litex.number`. The host here is `ℂ`, while `ha`
certifies that the object represents a real number. This is the Adapter's
instantiation for these native inputs; the generated theorem stays generic.

The premise has a corresponding conversion:

```lean
have hzC : (z : ℂ) ≠ 0 := fun h => hz (Complex.ofReal_injective h)
have h0 := Litex.NativeBridge.numberNonzero (M := M) (z : ℂ) hzC
```

Second, call the actual generated theorem:

```lean
have generated :=
  LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_source_x2e_lit.h_3
    (M := M) a ha b hb c hc h0
```

This obtains a proof of the identity. The later conversion consumes this
`generated` proof, so the final proof depends on the Litex compiler output.

Third, recover native equality. The Adapter uses `change` to unfold `Same`
into equality of denotations, then observes the certified operations using
only `M.add_numbers` and `M.div_numbers`. Two injectivity steps finish the
conversion:

```text
M.number A = M.number B
    ↓ M.number_injective
A = B                       (complex equality)
    ↓ Complex.ofReal_injective, with addition/division embedding laws
Real equality
```

The complete code's `simp only` uses only the representation laws listed here.
The Adapter does not reprove the distributive identity using `ring`,
`field_simp` or theorem search.

For an arbitrary representation, `Same` cannot simply be used as Lean's `=`.
This example first observes both sides numerically, then recovers native
equality through the proved injectivity of the numeric embedding. Sets and
functions require their own representation interfaces.

## 4. Use the result in an ordinary Lean proof

[UseInYourProject.lean](UseInYourProject.lean) imports only `Final`. It applies
the same theorem twice to obtain the three-term sum identity:

```lean
theorem threeTerms (x y t z : ℝ) (hz : z ≠ 0) :
    (x + y + t) / z = x / z + y / z + t / z := by
  calc
    (x + y + t) / z = (x + y) / z + t / z :=
      LitexLeanExample.quotientDistributes (x + y) t z hz
    _ = x / z + y / z + t / z := by
      rw [LitexLeanExample.quotientDistributes x y z hz]
```

This consumer needs no Litex object construction, membership proofs or direct
reference to `h_3`.

## Compare fairly with direct Lean

The same identity in ordinary Lean needs only:

```lean
theorem quotientDistributes (x y z : ℝ) :
    (x + y) / z = x / z + y / z := by
  exact add_div x y z
```

Lean division is total, so this identity does not even need a nonzero premise.
The Litex source requires a nonzero denominator to construct a valid division
object, and its exported interface preserves that condition. Generated proof
length does not measure what a Lean author would otherwise have to write;
the handwritten Adapter also has a real cost.

We also checked the fractional-linear map `f(x)=(x+1)/(x-1)`: for `x≠1`, prove
`f(x)≠1` and `f(f(x))=x`. This includes the domain condition needed to call the
function again, yet ordinary Lean remains concise. The checked proof body in
[DirectLean.lean](DirectLean.lean) is:

```lean
  unfold mobius
  constructor
  · intro h
    field_simp [sub_ne_zero.mpr hx] at h
    linarith
  · field_simp [sub_ne_zero.mpr hx]
    ring
```

The corresponding [complete Litex source](../../lean/examples/real_mobius_involution/statement.lit)
and [actual generated Lean](../../lean/examples/real_mobius_involution/statement.lean)
have passed strict verification, actual compilation, file-consistency checks
and pinned-version Lean checking. The formerly blocked difference-nonzero,
quotient-nonzero, difference-nonzero citation, and universal matching routes
for non-equality atomic conclusions and function calls are connected. The
source retains its mathematical proof without adding `trust`.

The key domain step in the source is:

```litex
forall x R:
    x != 1
    =>:
        x - 1 != 0
```

The quotient-nonzero step retains separate numerator and denominator proofs:

```litex
forall x R:
    x != 0
    =>:
        2 / x != 0
```

[Final.lean](Final.lean) provides an ordinary real-number interface whose proof
body calls Adapter:

```lean
noncomputable def mobius (x : ℝ) : ℝ := (x + 1) / (x - 1)

theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    mobius x ≠ 1 ∧ mobius (mobius x) = x := by
  simpa only [mobius] using Adapter.mobiusInvolution x hx
```

The Adapter selects the existing `Litex.NumericModel.model`, observes certified
function calls, and obtains native conclusions from the generated
domain-preservation and involution theorems. The ordinary Lake project, Final
and downstream uses have passed their checks; the compiled dependency audit
confirms that both generated theorems are actual proof dependencies. The
native definition uses Lean's real division. Its correspondence with the
restricted Litex function is used under the premise `x != 1`.

**This is the second connected Litex → Lean example; it does not establish that
authors write less code.** The direct Lean comparison uses seven tactic
statements, while the current Litex proof and handwritten Adapter also have
costs. Mathlib's [rational-expression and polynomial automation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html)
should remain in the comparison.

## Run and modify the example

This is an ordinary Lake project inside the complete repository. It uses Lean
4.31.0 and a pinned Mathlib version; [lakefile.toml](lakefile.toml) imports
Litex Core from the repository's `lean/` directory. The dependency configuration
has no machine-specific paths or local scripts dependencies.

See the [CLI documentation](../../docs/cli.md) for installation. Regenerate
from the **repository root**:

```sh
cargo build --release
target/release/litex -strict -lang en -f showcases/litex_to_lean_adapter/source.lit
target/release/litex -strict -lean -f showcases/litex_to_lean_adapter/source.lit > showcases/litex_to_lean_adapter/Generated.lean
target/release/litex -strict -lean -f lean/examples/real_mobius_involution/statement.lit > lean/examples/real_mobius_involution/statement.lean
```

Then run from this showcase directory:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Final.lean
lake env lean -DwarningAsError=true UseInYourProject.lean
```

For your own mathematical problem:

1. Write the statement and proof in a `.lit` file and have Litex verify it.
2. Regenerate Lean with the actual compiler; inspect the new exported
   signature, FactIds and premises.
3. In Adapter, encode the native inputs and premises, call the generated
   theorem, and convert its conclusion using proved observation interfaces.
   The compiler owns the generated file.
4. In Final, state the ordinary mathematics needed by users and call Adapter
   in the proof body.
5. Test downstream proofs from a file that imports only Final.

To connect this to an existing Mathlib project, first match Lean 4.31.0 and
the pinned Mathlib version (the exact commit is in lakefile.toml). Keep the
module names and include `Generated.lean`, `Adapter.lean`, `Final.lean`, and
the repository's `lean/Litex.lean` as the `Litex` module. For example, when
Core and the three modules are at the project root, add to `lakefile.toml`:

```toml
[[lean_lib]]
name = "Litex"
roots = ["Litex"]

[[lean_lib]]
name = "LitexExample"
roots = ["Final"]
globs = ["Generated", "Adapter", "Final"]
```

After `lake build LitexExample`, user files can `import Final`. If you move
the handwritten files into your own module directory, adjust the imports in
Adapter, Final and its consumers accordingly.

## Files and scope

| File | Maintainer | What it demonstrates |
|---|---|---|
| [source.lit](source.lit) | Mathematical author | Statement with domain conditions |
| [Generated.lean](Generated.lean) | Litex compiler | Actual proof interface, original FactIds and WD arguments |
| [Adapter.lean](Adapter.lean) | Interface author | Encode inputs, call the generated proof, observe the conclusion |
| [Final.lean](Final.lean) | Lean library author | Ordinary Mathlib statement and stable public interface |
| [UseInYourProject.lean](UseInYourProject.lean) | Lean consumer | Reuse the ordinary theorem in later proofs |
| [DirectLean.lean](DirectLean.lean) | Comparison author | Direct proof with common Mathlib interfaces for assessing complexity |

This example uses a handwritten Adapter over the numeric model and preserves
the source's nonzero premise. See [verification.json](verification.json) for
checks of the source, generated file and four proof layers.
