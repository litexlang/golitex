import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_function_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue (Litex.realUnaryValue (M := M) Real.sinh _raw_i2) (Litex.realUnaryValue (M := M) Real.cosh _raw_i2))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.sinh _value_i2 h_14);
    let _wd_1_1 := (Litex.cosh _value_i2 h_14);
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i2 h_14)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i2 h_14)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.sinh _value_i2 h_14);
    let _wd_1_1 := (Litex.cosh _value_i2 h_14);
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (Litex.sinh _value_i2 h_14)
      exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (Litex.cosh _value_i2 h_14)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.coshInRPos _atomic_wd_2_0)))))
    exact (Litex.addInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.sinhInR (_atomic_wd_1_0).val.left) (Litex.inRPos_real (_atomic_wd_1_0).val.right (Litex.coshInRPos (_atomic_wd_1_0).val.right))))))
theorem h_92 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_93 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_92 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro)

theorem h_94 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (M.number (1 : ℂ)) from by
          have _litex_residual : (M.addValue ((Litex.realUnaryValue (M := M) Real.sinh) (M.number (0 : ℂ))) ((Litex.realUnaryValue (M := M) Real.cosh) (M.number (0 : ℂ)))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sinh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)));
          let _wd_1_1 := (Litex.cosh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.sinh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (let _hyp := _atomic_wd_1_0; Litex.realToComplex _hyp (Litex.sinhInR _hyp))) (by
            let _atomic_wd_1_0 := (Litex.cosh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (let _hyp := _atomic_wd_1_0; Litex.realToComplex _hyp (Litex.coshInR _hyp)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) ((Real.sinh ((0 : ℂ)).re : ℂ) + (Real.cosh ((0 : ℂ)).re : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (let _hyp := (_equal_wd_2_0).val.left; Litex.denoteSinh _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (let _hyp := (_equal_wd_2_0).val.right; Litex.denoteCosh _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (M.addValue ((Litex.realUnaryValue (M := M) Real.sinh) (M.number (0 : ℂ))) ((Litex.realUnaryValue (M := M) Real.cosh) (M.number (0 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue (Litex.realUnaryValue (M := M) Real.sinh _raw_i2) (Litex.realUnaryValue (M := M) Real.cosh _raw_i2))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue (Litex.realUnaryValue (M := M) Real.sinh _raw_i2) (Litex.realUnaryValue (M := M) Real.cosh _raw_i2))) (Litex.denote _litex_literal.val.argument) = (M.addValue ((Litex.realUnaryValue (M := M) Real.sinh) (M.number (0 : ℂ))) ((Litex.realUnaryValue (M := M) Real.cosh) (M.number (0 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_function_x2f_statement_x2e_lit
