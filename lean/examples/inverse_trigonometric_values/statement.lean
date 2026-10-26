import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.arcsin (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.leOfSame (Litex.number (M := M) (-1 : ℂ)) (Litex.number (-1)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (show (-1 : ℂ) = (-1 : ℂ) from by norm_num))) rfl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) = (-1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.arcsin ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteArcsin _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Litex.nativeArccot, Real.arcsin_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w3 := (Litex.arcsin (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.leOfSame (Litex.number (M := M) (-1 : ℂ)) (Litex.number (-1)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (show (-1 : ℂ) = (-1 : ℂ) from by norm_num))) rfl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) = (-1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

noncomputable def _object_w4 := (Litex.div (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_16 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.arcsin ((1 : ℂ)).re : ℂ) ((Real.pi : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteArcsin _trig ((1 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (1 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num [Litex.nativeArccot, Real.arcsin_one, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
(Litex.arcsin _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.leOfSame _wd_1_0 (Litex.number (-1)) _wd_1_0 _wd_1_0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl (by
  let _atomic_wd_1_1 := _wd_1_0
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_1 _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.negInC (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_32 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.arcsin ((- (1 : ℂ))).re : ℂ) ((- (Real.pi : ℂ)) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteArcsin _trig ((- (1 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (- (1 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (Real.pi : ℂ)) ((_equal_wd_1_1).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num [Litex.nativeArccot, Real.arcsin_neg_one, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w7 := (Litex.arccos (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.leOfSame (Litex.number (M := M) (-1 : ℂ)) (Litex.number (-1)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (show (-1 : ℂ) = (-1 : ℂ) from by norm_num))) rfl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) = (-1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_59 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.arccos ((1 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteArccos _trig ((1 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (1 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Litex.nativeArccot, Real.arccos_one, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w8 := (Litex.arccos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.leOfSame (Litex.number (M := M) (-1 : ℂ)) (Litex.number (-1)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (show (-1 : ℂ) = (-1 : ℂ) from by norm_num))) rfl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) = (-1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_74 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.arccos ((0 : ℂ)).re : ℂ) ((Real.pi : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteArccos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w4 (M := M))).wd.1 ((_object_w4 (M := M))).wd.2.1 ((_object_w4 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num [Litex.nativeArccot, Real.arccos_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w9 := (let _wd_1_0 := ((_object_w5 (M := M))).val.arg;
(Litex.arccos _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.leOfSame _wd_1_0 (Litex.number (-1)) _wd_1_0 _wd_1_0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl (by
  let _atomic_wd_1_1 := _wd_1_0
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_1 _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))

theorem h_86 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (Real.pi : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (Real.pi : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (Real.pi : ℂ)) (Real.arccos ((- (1 : ℂ))).re : ℂ) (Real.pi : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteArccos _trig ((- (1 : ℂ))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (- (1 : ℂ)) _trig.wd.1 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (by norm_num [Litex.nativeArccot, Real.arccos_neg_one, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w11 := (Litex.arctan (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_104 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.arctan ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_1_0; Litex.denoteArctan _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Litex.nativeArccot, Real.arctan_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )

noncomputable def _object_w12 := (Litex.arccot (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_113 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeArccot ((0 : ℂ)).re : ℂ) ((Real.pi : ℂ) / (2 : ℂ)) (let _trig := _equal_wd_1_0; Litex.denoteArccot _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w4 (M := M))).wd.1 ((_object_w4 (M := M))).wd.2.1 ((_object_w4 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num [Litex.nativeArccot, Real.arctan_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_values_x2f_statement_x2e_lit
