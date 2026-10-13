import examples.newton_positive_update.statement

namespace Adapter

private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable abbrev newtonFunction := LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_positive_x5f_update_x2f_statement_x2e_lit._object_i2 (M := model)

private noncomputable def newtonCall (x : ℝ) (hx : 0 < x) :=
  let a := Litex.number (M := model) (x : ℂ)
  let ha := Litex.numberInRPos (M := model) x hx
  Litex.callTarget .real (Litex.denote (Litex.RPos (M := model)))
    (Litex.isSet (Litex.RPos (M := model))) Litex.positiveRealPredicate
    newtonFunction a (LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_positive_x5f_update_x2f_statement_x2e_lit.h_5603 (M := model))
    (Litex.inRPos_real a ha) ((Litex.positiveReal_members (Litex.denote a)).mp ha).2

private theorem newtonCallDenote (x : ℝ) (hx : 0 < x) :
    Litex.denote (newtonCall x hx) = model.number (((x + 2 / x) / 2 : ℝ) : ℂ) := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.numberInRPos (M := model) x hx
  have hd : model.mem (Litex.denote a) newtonFunction.val.signature.domain :=
    (Litex.FunctionSignature.oneTarget_domain .real
      (Litex.denote (Litex.RPos (M := model))) (Litex.isSet (Litex.RPos (M := model)))
      Litex.positiveRealPredicate _).mpr
      ⟨Litex.inRPos_real a ha, ((Litex.positiveReal_members (Litex.denote a)).mp ha).2⟩
  have beta := Litex.FunctionSemantics.call_graphValue
    newtonFunction.val.signature.domain newtonFunction.val.signature.target
    newtonFunction.val.bodyValue newtonFunction.wd (Litex.denote a) hd
  change Litex.denote (newtonCall x hx) =
    model.divValue (model.addValue (model.number (x : ℂ))
      (model.divValue (model.number 2) (model.number (x : ℂ)))) (model.number 2) at beta
  have hxC : (x : ℂ) ≠ 0 := fun h => (ne_of_gt hx)
    (Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using h))
  rw [model.div_numbers _ _ hxC, model.add_numbers,
    model.div_numbers _ _ (by norm_num)] at beta
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using beta

/-- Positivity comes from the generated positive-codomain theorem. The only
handwritten work observes the same owned graph call as a native real value. -/
theorem newtonPositive (x : ℝ) (hx : 0 < x) :
    0 < (x + 2 / x) / 2 := by
  let a := Litex.number (M := model) (x : ℂ)
  have ha := Litex.numberInRPos (M := model) x hx
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_positive_x5f_update_x2f_statement_x2e_lit.h_5606 (M := model) a ha
  change Litex.In (newtonCall x hx) (Litex.RPos (M := model)) at generated
  have positive := Litex.inRPos_positive (newtonCall x hx) generated
  exact (Litex.NativeBridge.lt_iff_ofDenoteReal (Litex.number 0)
    (newtonCall x hx) 0 ((x + 2 / x) / 2) rfl (newtonCallDenote x hx)).mp positive

end Adapter
