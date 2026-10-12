import Generated
import examples.real_mobius_involution.statement

namespace Adapter

/-- The public interface already uses ordinary real arithmetic. -/
theorem quotientDistributes (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  -- 1. Choose a proved interpretation and encode the inputs and source facts.
  let M := Litex.NumericModel.model
  let a := Litex.number (M := M) (x : ℂ)
  let b := Litex.number (M := M) (y : ℂ)
  let c := Litex.number (M := M) (z : ℂ)
  have ha := Litex.NativeBridge.numberInR (M := M) x
  have hb := Litex.NativeBridge.numberInR (M := M) y
  have hc := Litex.NativeBridge.numberInR (M := M) z
  have hzC : (z : ℂ) ≠ 0 := fun h => hz (Complex.ofReal_injective h)
  have h0 := Litex.NativeBridge.numberNonzero (M := M) (z : ℂ) hzC

  -- 2. Consume the actual compiler-generated theorem and its required facts.
  have generated :=
    LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_source_x2e_lit.h_3
      (M := M) a ha b hb c hc h0

  -- 3. Observe the certified operations, then use the two injective embeddings.
  change M.divValue (M.addValue (M.number (x : ℂ)) (M.number (y : ℂ)))
      (M.number (z : ℂ)) =
    M.addValue (M.divValue (M.number (x : ℂ)) (M.number (z : ℂ)))
      (M.divValue (M.number (y : ℂ)) (M.number (z : ℂ))) at generated
  simp only [M.add_numbers, M.div_numbers _ _ hzC] at generated
  have native : ((x : ℂ) + (y : ℂ)) / (z : ℂ) =
      (x : ℂ) / (z : ℂ) + (y : ℂ) / (z : ℂ) :=
    M.number_injective generated
  exact Complex.ofReal_injective
    (by simpa only [Complex.ofReal_add, Complex.ofReal_div] using native)

private noncomputable abbrev mobiusModel := Litex.NumericModel.model

private noncomputable def mobiusCall {α : Type*}
    [Litex.Representation mobiusModel α]
    (a : Litex.Obj (M := mobiusModel) α) (ha : Litex.In a Litex.R)
    (h1 : ¬ Litex.Same a (Litex.number 1)) :=
  Litex.call .real .real (fun x => x ≠ mobiusModel.number 1)
    (LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit._object_i2 (M := mobiusModel))
    a (LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit.h_352 (M := mobiusModel)) ha h1

private theorem mobiusCallDenote {α : Type*}
    [Litex.Representation mobiusModel α]
    (a : Litex.Obj (M := mobiusModel) α) (ha : Litex.In a Litex.R)
    (h1 : ¬ Litex.Same a (Litex.number 1)) (x : ℝ) (hx : x ≠ 1)
    (hv : Litex.denote a = mobiusModel.number (x : ℂ)) :
    Litex.denote (mobiusCall a ha h1) =
      mobiusModel.number (((x + 1) / (x - 1) : ℝ) : ℂ) := by
  let f := LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit._object_i2 (M := mobiusModel)
  have domain : mobiusModel.mem (Litex.denote a) f.val.signature.domain :=
    (Litex.FunctionSignature.one_domain .real .real (fun x => x ≠ mobiusModel.number 1) _).mpr ⟨ha, h1⟩
  have beta := Litex.FunctionSemantics.call_graphValue f.val.signature.domain
    f.val.signature.target f.val.bodyValue f.wd (Litex.denote a) domain
  change Litex.denote (mobiusCall a ha h1) =
    mobiusModel.divValue (mobiusModel.addValue (Litex.denote a) (mobiusModel.number 1))
      (mobiusModel.subValue (Litex.denote a) (mobiusModel.number 1)) at beta
  have hxC : (x : ℂ) ≠ 1 := fun h =>
    hx (Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using h))
  rw [hv, mobiusModel.add_numbers, mobiusModel.sub_numbers,
    mobiusModel.div_numbers _ _ (sub_ne_zero.mpr hxC)] at beta
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one] using beta

/-- Convert the generated domain-preservation and involution proofs to real arithmetic. -/
theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    (x + 1) / (x - 1) ≠ 1 ∧
      (((x + 1) / (x - 1)) + 1) / (((x + 1) / (x - 1)) - 1) = x := by
  let a := Litex.number (M := mobiusModel) (x : ℂ)
  have ha := Litex.NativeBridge.numberInR (M := mobiusModel) x
  have hxC : (x : ℂ) ≠ 1 := fun h =>
    hx (Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using h))
  have h1 := Litex.NativeBridge.notSameOfDenoteNumber a
    (Litex.number (M := mobiusModel) 1) (x : ℂ) 1 rfl rfl hxC
  have preserved := LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit.h_424
    (M := mobiusModel) a ha h1
  have firstValue := mobiusCallDenote a ha h1 x hx rfl
  have nativeGuard : (x + 1) / (x - 1) ≠ 1 := by
    intro h
    apply preserved
    change Litex.denote (mobiusCall a ha h1) = mobiusModel.number 1
    rw [firstValue]
    exact congrArg mobiusModel.number
      (by simpa only [Complex.ofReal_one] using congrArg (fun r : ℝ => (r : ℂ)) h)
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit.h_3588
    (M := mobiusModel) a ha h1
  have secondValue := mobiusCallDenote (mobiusCall a ha h1)
    (Litex.callInOutput _) preserved ((x + 1) / (x - 1)) nativeGuard firstValue
  change Litex.denote (mobiusCall (mobiusCall a ha h1)
    (Litex.callInOutput _) preserved) = mobiusModel.number (x : ℂ) at generated
  rw [secondValue] at generated
  exact ⟨nativeGuard, Complex.ofReal_injective (mobiusModel.number_injective generated)⟩

end Adapter
