import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_real_x5f_order_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

noncomputable def _object_w2 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_1_0 _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (3 : ℝ)) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (2 : ℝ)) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
      )
  )

theorem h_19 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_object_w2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (_object_w1 (M := M)) (_object_w2 (M := M)) (by
          let _atomic_wd_1_1 := (_object_w1 (M := M))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (3 : ℝ)) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_1 (M := M)))
      )
  )

theorem h_20 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
      )
  )

theorem h_23 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (h_20 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_real_x5f_order_x2f_statement_x2e_lit
