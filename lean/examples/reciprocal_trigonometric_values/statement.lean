import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_trigonometric_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.sec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.nativeSec ((0 : ℂ)).re : ℂ) (1 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteSec _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num [Litex.nativeSec]))))
      )
  )

noncomputable def _object_w3 := (Litex.sec (Litex.number (M := M) (Real.pi : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (by
  let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (Real.pi : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((Real.pi : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((Real.pi : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Real.pi : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((Real.pi : ℂ)).re = ((Real.pi - (0))) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))

noncomputable def _object_w4 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_19 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeSec ((Real.pi : ℂ)).re : ℂ) (- (1 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSec _trig ((Real.pi : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Real.pi : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num [Litex.nativeSec]))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.csc _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_0;
  (Litex.sin _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.divInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.sin (((Real.pi : ℂ) / (2 : ℂ))).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteSin _trig (((Real.pi : ℂ) / (2 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((Real.pi : ℂ) / (2 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : (((Real.pi : ℂ) / (2 : ℂ))).re = (Real.pi / 2) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))

theorem h_70 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.nativeCsc (((Real.pi : ℂ) / (2 : ℂ))).re : ℂ) (1 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteCsc _trig (((Real.pi : ℂ) / (2 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((Real.pi : ℂ) / (2 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num [Litex.nativeCsc]))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_trigonometric_x5f_values_x2f_statement_x2e_lit
