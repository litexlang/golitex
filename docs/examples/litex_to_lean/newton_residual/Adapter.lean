import examples.newton_residual_identity.statement

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable abbrev newtonFunction := LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_identity_x2f_statement_x2e_lit._object_i1 (M := model)

private noncomputable def newtonCall {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.R)
    (h0 : ¬ Litex.Same a (Litex.number 0)) :=
  Litex.call .real .real (fun raw => raw ≠ model.number 0) newtonFunction a
    (LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_identity_x2f_statement_x2e_lit.h_357 (M := model)) ha h0

private theorem newtonCallDenote {α : Type*} [Litex.Representation model α]
    (a : Litex.Obj (M := model) α) (ha : Litex.In a Litex.R)
    (h0 : ¬ Litex.Same a (Litex.number 0))
    (x : ℝ) (hx : x ≠ 0) (hvalue : Litex.denote a = model.number (x : ℂ)) :
    Litex.denote (newtonCall a ha h0) = model.number (((x + 2 / x) / 2 : ℝ) : ℂ) := by
  have hd : model.mem (Litex.denote a) newtonFunction.val.signature.domain :=
    (Litex.FunctionSignature.one_domain .real .real (fun raw => raw ≠ model.number 0) _).mpr ⟨ha, h0⟩
  have beta := Litex.FunctionSemantics.call_graphValue
    newtonFunction.val.signature.domain newtonFunction.val.signature.target
    newtonFunction.val.bodyValue newtonFunction.wd (Litex.denote a) hd
  change Litex.denote (newtonCall a ha h0) =
    model.divValue (model.addValue (Litex.denote a)
      (model.divValue (model.number 2) (Litex.denote a))) (model.number 2) at beta
  have hxC : (x : ℂ) ≠ 0 := fun h => hx (Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using h))
  rw [hvalue, model.div_numbers _ _ hxC, model.add_numbers,
    model.div_numbers _ _ (by norm_num)] at beta
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using beta

theorem newtonResidualIdentity (x : ℝ) (hx : x ≠ 0) :
    ((x + 2 / x) / 2)^2 - 2 = ((x - 2 / x) / 2)^2 := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.NativeBridge.numberInR (M := model) x
  have hxC : (x : ℂ) ≠ 0 := fun h => hx (Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using h))
  have h0 : ¬ Litex.Same a (Litex.number 0) := Litex.NativeBridge.numberNonzero (x : ℂ) hxC
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_identity_x2f_statement_x2e_lit.h_361 (M := model) a ha h0
  have observed := newtonCallDenote a ha h0 x hx rfl
  have powTwo (z : ℂ) : model.powValue (model.number z) (model.number 2) =
      model.number (z ^ 2) := by
    simpa only [Nat.cast_ofNat] using model.pow_numbers_nat z 2
  change model.subValue (model.powValue (Litex.denote (newtonCall a ha h0)) (model.number 2))
    (model.number 2) =
    model.powValue (model.divValue (model.subValue (model.number (x : ℂ))
      (model.divValue (model.number 2) (model.number (x : ℂ)))) (model.number 2))
      (model.number 2) at generated
  rw [observed, powTwo, model.sub_numbers,
    model.div_numbers _ _ hxC, model.sub_numbers,
    model.div_numbers _ _ (by norm_num), powTwo] at generated
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using model.number_injective generated

end Adapter
