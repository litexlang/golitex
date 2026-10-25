import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_functions_x2f_statement_x2e_lit

universe u v3 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.sin _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sin _value_i2 h_14)
    exact (Litex.sinInR _atomic_wd_1_0))))
theorem h_32 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_33 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro)

theorem h_34 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.realUnaryValue (M := M) Real.sin) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (Litex.sin (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Real.sin ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_2_0; Litex.denoteSin _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = ((Litex.realUnaryValue (M := M) Real.sin) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.sin) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_71 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_84 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _object_w13 := (let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_32 (M := M)) h_84 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w8 (h_32 (M := M)) (by
    let _atomic_wd_1_0 := _object_w8
    exact (by
      let _litex_return_call := _object_w8
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  let _object_w14 := (let _wd_1_0 := (Litex.sin _value_i3 h_84);
  (Litex.sin _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.sin _value_i3 h_84)
    exact (Litex.sinInR _atomic_wd_1_0))))
  exact (by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_84
          let _object_w13 := (let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_32 (M := M)) h_84 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w8 (h_32 (M := M)) (by
            let _atomic_wd_1_0 := _object_w8
            exact (by
              let _litex_return_call := _object_w8
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          let _object_w14 := (let _wd_1_0 := (Litex.sin _value_i3 h_84);
          (Litex.sin _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.sin _value_i3 h_84)
            exact (Litex.sinInR _atomic_wd_1_0))))
          have h_70 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.sin) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) from by
                    have _litex_residual : ((Litex.realUnaryValue (M := M) Real.sin) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.sin) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3)) from by
                    let _litex_original := (_equal_wd_1_0).val.argument
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_84 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3)) from rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.sin) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) from by
                    let _litex_original := (let _object_w11 := (Litex.sin _value_i3 h_84);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w11 (h_32 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w11
                      exact (Litex.sinInR _atomic_wd_1_0)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w12 := (Litex.sin _value_i3 h_84);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w12 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w12
                      exact (Litex.sinInR _atomic_wd_1_0)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.sin _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.sin) ((Litex.realUnaryValue (M := M) Real.sin) (Litex.denote _value_i3))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_70
        )
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.tan _raw_i5)) (by
  intro _raw_i5 h_1433 h_371
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1433)
  have h_1433 : Litex.In _value_i5 (Litex.R (M := M)) := h_1433
  have h_371 : ¬ Litex.Same (Litex.cos _value_i5 h_1433) (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))
            exact h_371)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.tan _value_i5 h_1433 (by
      let _atomic_wd_2_0 := (Litex.cos _value_i5 h_1433)
      exact h_371))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.tan _value_i5 h_1433 (by
      let _atomic_wd_2_0 := (Litex.cos _value_i5 h_1433)
      exact h_371))
    exact (Litex.tanInR _atomic_wd_1_0))))
theorem h_1475 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_1476 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))) (_object_i4 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_1475 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))

theorem h_1477 : (by
  let _equal_wd_1_0 := (_object_w22 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w22 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.realUnaryValue (M := M) Real.tan) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (Litex.tan (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Real.tan ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_2_0; Litex.denoteTan _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * Real.pi := (by (conv_lhs => norm_num); ring); rw [_angle, Real.tan_add_int_mul_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))) = ((Litex.realUnaryValue (M := M) Real.tan) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := (Litex.cos _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1476 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.tan _raw_i5)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i5) = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.tan _raw_i5)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.tan) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_1660 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1674 : Litex.In _value_i7 (Litex.R (M := M))), (by
  let _object_w24 := (let _wd_1_0 := (Litex.sin _value_i7 h_1674);
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.sin _value_i7 h_1674)
    exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w25 := (Litex.sin _value_i7 h_1674)
  exact (by
    let _equal_wd_1_0 := _object_w24
    let _equal_wd_1_1 := _object_w25
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_1674
          let _object_w24 := (let _wd_1_0 := (Litex.sin _value_i7 h_1674);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.sin _value_i7 h_1674)
            exact (M.real_subset_complex _ (Litex.sinInR _atomic_wd_1_0))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w25 := (Litex.sin _value_i7 h_1674)
          have h_1659 : (by
            let _equal_wd_1_0 := _object_w24
            let _equal_wd_1_1 := _object_w25
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w24;
                  let _equal_wd_1_1 := _object_w25;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Real.sin ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674))).re : ℂ) + (0 : ℂ)) (Real.sin ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674))).re : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _trig := (_equal_wd_1_0).val.left; Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_1674)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _trig := _equal_wd_1_1; Litex.denoteSin _trig ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1674)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_1674)))) (by ring!))))
                )
            )
          exact h_1659
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_functions_x2f_statement_x2e_lit
