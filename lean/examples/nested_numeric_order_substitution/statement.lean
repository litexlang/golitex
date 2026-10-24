import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_numeric_x5f_order_x5f_substitution_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
      )
  )

noncomputable def _object_i2 := (Litex.number (M := M) (3 : ℂ))
theorem h_9 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
      )
  )
theorem h_10 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.mul (_object_i1 (M := M)) (_object_i1 (M := M)) (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_3 (M := M))));
let _wd_1_1 := (_object_i2 (M := M));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.mulInC (_object_i1 (M := M)) (_object_i1 (M := M)) (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_3 (M := M))))) (M.real_subset_complex _ (h_9 (M := M)))))

theorem h_11 : (by
  let _atomic_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w5 (M := M))
          exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue (h_4 (M := M)) (h_4 (M := M))) (h_10 (M := M)))).symm (Litex.sameRefl (Litex.number (M := M) (7 : ℂ))) (by
            let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_3_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ))))
            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (7 : ℂ)) (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (7 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (7 : ℝ) (by norm_num)))) = (7 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + (3 : ℂ)) (7 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (3 : ℂ)) (by
              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) = (7 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_numeric_x5f_order_x5f_substitution_x2f_statement_x2e_lit
