# Expected targets and native Lean reuse

`Statements.lit` contains common source statements. `ExpectedTarget.lean` is
handwritten expected compiler output, checked against the current Core. No
automatic emitter or verifier-result replay produced it. Separate successful
source and Lean checks demonstrate these interfaces, not compiler correctness.

The ownership path in this example is:

```text
Statements.lit -> ExpectedTarget.lean -> Adapter.lean -> Final.lean
                            Core + NumericModel
```

## Source to target

Each target declaration is conditional on a fixed `M : Litex.Semantics`.
Generic source objects retain `a : Litex.Obj α` and their registered
`Representation M α`; membership is an ordinary proposition.

| Source | Target declaration / conclusion |
| --- | --- |
| `1 = 1` | `oneSelf`: `Same (number 1) (number 1)` |
| `$is_set(1)` | `oneIsSet`: `IsSet (number 1)` |
| `1 $in R` | `oneInR`: `In (number 1) R` |
| `forall a C: a = a` | `complexSelf`: certified a plus `In a C` implies `Same a a` |
| `forall a R: a $in C` | `realInComplex`: `In a R` implies `In a C`, keeping the same a and α |
| `forall a C: a + 0 = a` | `addZero`: semantic equality of the owned addition and a |
| `forall a C, b C: b != 0 => a/b = a/b` | `quotientSelf`: owned division receives both memberships and semantic nonzero |

The table abbreviates multiline source formatting; the exact source is in
Statements.lit. For example, the addition target is:

```lean
theorem addZero {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    Same (add a (number 0) haC (numberInC 0)) a :=
  Litex.addZero a haC
```

Here a already contains its WD. The addition contains its two certified
children, and its root WD contains both memberships. The Core law derives the
equality from the explicit semantic contract; matching that law to a current
Rust verifier certificate is later compiler work.

`have a C` introduces a source context object and its membership fact. In a
target theorem, those appear as the same generic a/haC arguments above. These
examples do not implement the statement executor or closed-module witness
selection for a standalone `have` declaration.

## Native interface

`Litex/NativeBridge.lean` supplies proved conversions:

- Native complex input z becomes `Litex.number z`, preserving its native payload.
- A native real input r embeds as `Litex.number (r : ℂ)`, with proved R-membership.
- Semantic equality of native numeric leaves yields native equality through
  the model's injective numeric interpretation. There is no generic Same-to-host-Eq rule.
- Owned addition/division equalities convert to native `+`/`/` equalities.
- A generic a with C-membership has a unique native complex view `asComplex a haC`,
  with a denotation law and proof-independence theorem. It does not replace a or α.

For example, `Adapter.complexAddZero` packs a native complex input, invokes
`ExpectedTarget.addZero`, and unwraps the returned Same proof using
`NativeBridge.addSame_iff`. It does not re-prove the arithmetic goal. The real
version also consumes `ExpectedTarget.realInComplex` and transports native casts.

`Final.lean` presents ordinary Lean/Mathlib statements:

```lean
theorem complexAddZero (x : ℂ) : x + 0 = x := by
  exact Adapter.complexAddZero x

theorem realAddZero (x : ℝ) : x + 0 = x := by
  exact Adapter.realAddZero x
```

No model, representation, WD or bridge assumptions occur in those statements.
The consumer also uses the exported equality with ordinary `rw` inside a
native function application.

## Concrete interpretation and scope

To close the native theorems, Adapter explicitly chooses the **example-only**
`NumericModel.model` inside its proof. This is a proved inhabitant of the
current Semantics contract, rather than a new assumed default instance.

The model uses actual Mathlib ZFSet values and membership. Native complex
values embed injectively through a chosen well-order and ordinal encoding;
N/Z/Q/R/C are actual ranges of embedded native numbers. Arithmetic decodes,
uses native numeric operations, then re-encodes. Decoding is a function of the
value alone, with a round-trip law. Outside C it defaults to zero solely to
totalize the internal model fields; public constructors still require their
actual WD/domain conditions.

All model values are already ZF sets, so its IsSet predicate is True. Same
remains genuine equality of denotations and In remains genuine ZF membership.
The numeric codes' own membership reflects the chosen well-order. This is a
demonstration interpretation of the current numeric contract, not a selected
production encoding or a proof that every Litex constructor/foundation agrees
with it. Sets, functions and the complete source axiom system need further work.

## Check

From the repository root, with pinned cached Mathlib available:

```sh
python3 lean/check.py
target/release/litex -strict -lang en -f lean/InteropExamples/Statements.lit
```

The Lean gate compiles ExpectedTarget, NumericModel, Adapter and Final, checks
four rejected evidence/host-equality boundaries, audits 19 public declarations,
and inspects the compiled adapter for its live target-theorem dependency.
It writes only workspace-local outputs and excludes archived Litex libraries.
The source check is separately recorded in `proof_journals/statements.json`.

On October 8, 2026, all 14 Lean files passed with Lean 4.31.0 and warnings as
errors; all four negative fixtures were rejected. The 19 audited declarations
depend only on `propext`, `Classical.choice` and `Quot.sound`. The compiled
adapter's live expected-target dependency and a normal
`lake env lean -DwarningAsError=true InteropExamples/Final.lean` check also
passed. The strict source gate accepted all seven statements with no session error.

In a normally initialized Lake project, `lake build Litex InteropExamples`
builds both libraries. Ordinary native users can import
`InteropExamples.Final`; a future production adapter will expose the same
native-facing pattern for actual compiler-produced proofs.
