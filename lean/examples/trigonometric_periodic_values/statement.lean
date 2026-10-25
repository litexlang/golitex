import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_periodic_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (13 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (13 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (6 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (13 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (13 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.sin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (6 : ℂ)) (Litex.mulInR (Litex.number (M := M) (13 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (13 : ℂ) (13 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w2 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sin ((((13 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re : ℂ) ((1 : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSin _trig ((((13 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((13 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (13 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (13 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : ((((13 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re = (Real.pi / 6) + (1 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.negInC (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.cos _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (3 : ℂ)) (Litex.negInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

theorem h_36 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.cos (((- (Real.pi : ℂ)) / (3 : ℂ))).re : ℂ) ((1 : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteCos _trig (((- (Real.pi : ℂ)) / (3 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((- (Real.pi : ℂ)) / (3 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w2 (M := M))).wd.1 ((_object_w2 (M := M))).wd.2.1 ((_object_w2 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : (((- (Real.pi : ℂ)) / (3 : ℂ))).re = ((2 * Real.pi - (Real.pi / 3))) + (-1 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w4 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (4 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.tan _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (4 : ℂ)) (Litex.mulInR (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_0;
  (Litex.cos _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.divInR (_atomic_wd_2_0).val.left (Litex.number (M := M) (4 : ℂ)) (Litex.mulInR (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_atomic_wd_1_0).val.arg).val.left (Litex.number (M := M) (4 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_atomic_wd_1_0).val.arg).val.left).wd.1 (((_atomic_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re = (Real.pi / 4) + (1 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))

theorem h_61 : (by
  let _equal_wd_1_0 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Real.tan ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re : ℂ) (1 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteTan _trig ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by have _angle : ((((9 : ℂ) * (Real.pi : ℂ)) / (4 : ℂ))).re = (Real.pi / 4) + (2 : ℤ) * Real.pi := (by (conv_lhs => norm_num); ring); rw [_angle, Real.tan_add_int_mul_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.sin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w7 := (let _wd_1_0 := (Litex.sqrt (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (M.real_subset_complex _ (by
    let _litex_sqrt := _atomic_wd_1_0
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  ))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_124 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  let _equal_wd_1_1 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M));
        let _equal_wd_1_1 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sin (((Real.pi : ℂ) / (4 : ℂ))).re : ℂ) ((Real.sqrt (2 : ℝ) : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSin _trig (((Real.pi : ℂ) / (4 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((Real.pi : ℂ) / (4 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _litex_sqrt := (_equal_wd_1_1).val.left;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 (2 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : (((Real.pi : ℂ) / (4 : ℂ))).re = (Real.pi / 4) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w8 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.tan _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_0;
  (Litex.cos _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.divInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos (((Real.pi : ℂ) / (6 : ℂ))).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig (((Real.pi : ℂ) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((Real.pi : ℂ) / (6 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (6 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : (((Real.pi : ℂ) / (6 : ℂ))).re = (Real.pi / 6) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))

noncomputable def _object_w9 := (let _wd_1_0 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (M.real_subset_complex _ (by
    let _litex_sqrt := _atomic_wd_1_0
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  ))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_150 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  let _equal_wd_1_1 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        let _equal_wd_1_1 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tan (((Real.pi : ℂ) / (6 : ℂ))).re : ℂ) ((Real.sqrt (3 : ℝ) : ℂ) / (3 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteTan _trig (((Real.pi : ℂ) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((Real.pi : ℂ) / (6 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _litex_sqrt := (_equal_wd_1_1).val.left;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 (3 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by have _angle : (((Real.pi : ℂ) / (6 : ℂ))).re = (Real.pi / 6) + (0 : ℤ) * Real.pi := (by (conv_lhs => norm_num); ring); rw [_angle, Real.tan_add_int_mul_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w10 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (6 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.sin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (6 : ℂ)) (Litex.mulInR (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w11 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_189 : (by
  let _equal_wd_1_0 := (_object_w10 (M := M))
  let _equal_wd_1_1 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w10 (M := M));
        let _equal_wd_1_1 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sin ((((7 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re : ℂ) ((- (1 : ℂ)) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSin _trig ((((7 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((7 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : ((((7 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re = ((Real.pi + (Real.pi / 6))) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w12 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.cos _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (3 : ℂ)) (Litex.mulInR (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

theorem h_226 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  let _equal_wd_1_1 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        let _equal_wd_1_1 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.cos ((((2 : ℂ) * (Real.pi : ℂ)) / (3 : ℂ))).re : ℂ) ((- (1 : ℂ)) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteCos _trig ((((2 : ℂ) * (Real.pi : ℂ)) / (3 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((2 : ℂ) * (Real.pi : ℂ)) / (3 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))))) (Litex.NativeBridge.denoteDiv ((_object_w11 (M := M))).val.left (Litex.number (M := M) (2 : ℂ)) ((_object_w11 (M := M))).wd.1 ((_object_w11 (M := M))).wd.2.1 ((_object_w11 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (((_object_w11 (M := M))).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : ((((2 : ℂ) * (Real.pi : ℂ)) / (3 : ℂ))).re = ((Real.pi - (Real.pi / 3))) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w13 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (6 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.tan _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (6 : ℂ)) (Litex.mulInR (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_0;
  (Litex.cos _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.divInR (_atomic_wd_2_0).val.left (Litex.number (M := M) (6 : ℂ)) (Litex.mulInR (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_atomic_wd_1_0).val.arg).val.left (Litex.number (M := M) (6 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_atomic_wd_1_0).val.arg).val.left).wd.1 (((_atomic_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re = ((Real.pi - (Real.pi / 6))) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))

noncomputable def _object_w14 := (let _wd_1_0 := (let _wd_2_0 := ((_object_w9 (M := M))).val.left;
(Litex.neg _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (M.real_subset_complex _ (by
    let _litex_sqrt := _atomic_wd_1_0
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  )))));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.negInC (_atomic_wd_1_0).val.arg (M.real_subset_complex _ (by
    let _litex_sqrt := (_atomic_wd_1_0).val.arg
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  )))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_258 : (by
  let _equal_wd_1_0 := (_object_w13 (M := M))
  let _equal_wd_1_1 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w13 (M := M));
        let _equal_wd_1_1 := (_object_w14 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tan ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re : ℂ) ((- (Real.sqrt (3 : ℝ) : ℂ)) / (3 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteTan _trig ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg ((_equal_wd_1_1).val.left).val.arg ((_equal_wd_1_1).val.left).wd _ (let _litex_sqrt := ((_equal_wd_1_1).val.left).val.arg;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 (3 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by have _angle : ((((5 : ℂ) * (Real.pi : ℂ)) / (6 : ℂ))).re = ((Real.pi - (Real.pi / 6))) + (0 : ℤ) * Real.pi := (by (conv_lhs => norm_num); ring); rw [_angle, Real.tan_add_int_mul_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w15 := (let _wd_1_0 := (let _wd_2_0 := (((_object_w3 (M := M))).val.arg).val.left;
let _wd_2_1 := (Litex.number (M := M) (4 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.negInC (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.sin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (4 : ℂ)) (Litex.negInR (Litex.number (M := M) (Real.pi : ℂ)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w16 := (let _wd_1_0 := (let _wd_2_0 := ((_object_w7 (M := M))).val.left;
(Litex.neg _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (M.real_subset_complex _ (by
    let _litex_sqrt := _atomic_wd_1_0
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  )))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.negInC (_atomic_wd_1_0).val.arg (M.real_subset_complex _ (by
    let _litex_sqrt := (_atomic_wd_1_0).val.arg
    exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
  )))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_346 : (by
  let _equal_wd_1_0 := (_object_w15 (M := M))
  let _equal_wd_1_1 := (_object_w16 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w15 (M := M));
        let _equal_wd_1_1 := (_object_w16 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sin (((- (Real.pi : ℂ)) / (4 : ℂ))).re : ℂ) ((- (Real.sqrt (2 : ℝ) : ℂ)) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSin _trig (((- (Real.pi : ℂ)) / (4 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg ((- (Real.pi : ℂ)) / (4 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg ((_equal_wd_1_1).val.left).val.arg ((_equal_wd_1_1).val.left).wd _ (let _litex_sqrt := ((_equal_wd_1_1).val.left).val.arg;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 (2 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)))))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by have _angle : (((- (Real.pi : ℂ)) / (4 : ℂ))).re = ((2 * Real.pi - (Real.pi / 4))) + (-1 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )

noncomputable def _object_w17 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.mulInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.sin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.mulInR (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.inRPos_real (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w18 := ((_object_w11 (M := M))).val.left

theorem h_396 : (by
  let _equal_wd_1_0 := (_object_w17 (M := M))
  let _equal_wd_1_1 := (_object_w18 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w17 (M := M));
        let _equal_wd_1_1 := (_object_w18 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.sin ((((3 : ℂ) * (Real.pi : ℂ)) / (2 : ℂ))).re : ℂ) (- (1 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteSin _trig ((((3 : ℂ) * (Real.pi : ℂ)) / (2 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (((3 : ℂ) * (Real.pi : ℂ)) / (2 : ℂ)) _trig.wd (Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by have _angle : ((((3 : ℂ) * (Real.pi : ℂ)) / (2 : ℂ))).re = ((Real.pi + (Real.pi / 2))) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.sin_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_periodic_x5f_values_x2f_statement_x2e_lit
