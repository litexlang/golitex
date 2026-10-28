import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_product_x5f_integer_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_17 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sqrt (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (12 : ℂ) Litex.R (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (12 : ℂ) (12 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num)) = (12 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (27 : ℂ)) (27 : ℂ) Litex.R (show (M.number (27 : ℂ)) = M.number (27 : ℂ) from (congrArg M.number (show (27 : ℂ) = (27 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (27 : ℂ) (27 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) = (27 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (27 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.mul _wd_1_0 _wd_1_1 (let _litex_sqrt := _wd_1_0;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member) (let _litex_sqrt := _wd_1_1;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (18 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sqrt (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (12 : ℂ) Litex.R (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (12 : ℂ) (12 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num)) = (12 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (27 : ℂ)) (27 : ℂ) Litex.R (show (M.number (27 : ℂ)) = M.number (27 : ℂ) from (congrArg M.number (show (27 : ℂ) = (27 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (27 : ℂ) (27 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) = (27 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (27 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.mul _wd_1_0 _wd_1_1 (let _litex_sqrt := _wd_1_0;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member) (let _litex_sqrt := _wd_1_1;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (18 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (18 : ℂ)) from ((show Litex.denote _equal_wd_1_0 = (M.mulValue (Litex.sqrtValue (M := M) (M.number (12 : ℂ))) (Litex.sqrtValue (M := M) (M.number (27 : ℂ)))) from congrArg₂ M.mulValue (show Litex.denote (_equal_wd_1_0).val.left = (Litex.sqrtValue (M := M) (M.number (12 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (12 : ℂ)) = (M.number (12 : ℂ)) from rfl)) (show Litex.denote (_equal_wd_1_0).val.right = (Litex.sqrtValue (M := M) (M.number (27 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (27 : ℂ)) = (M.number (27 : ℂ)) from rfl)))).trans (((Eq.refl (M.mulValue (Litex.sqrtValue (M := M) (M.number (12 : ℂ))) (Litex.sqrtValue (M := M) (M.number (27 : ℂ)))))).trans ((((congrArg₂ M.mulValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (12 : ℂ) = (((12 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (12 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (27 : ℂ)) = M.number (27 : ℂ) from (congrArg M.number (show (27 : ℂ) = (27 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (27 : ℂ) = (((27 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (27 : ℝ))))).trans (M.mul_numbers ((Real.sqrt (12 : ℝ) : ℝ) : ℂ) ((Real.sqrt (27 : ℝ) : ℝ) : ℂ)))).trans ((congrArg M.number (by
          have _litex_product : Real.sqrt (12 : ℝ) * Real.sqrt (27 : ℝ) = (18 : ℝ) := by
            rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (12 : ℝ))]
            apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
            norm_num
          exact_mod_cast _litex_product : (((Real.sqrt (12 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (27 : ℝ) : ℝ) : ℂ)) = (18 : ℂ))).trans (((show (M.number (18 : ℂ)) = M.number (18 : ℂ) from (congrArg M.number (show (18 : ℂ) = (18 : ℂ) from by norm_num)))).symm.trans ((show Litex.denote (Litex.number (M := M) (18 : ℂ)) = (M.number (18 : ℂ)) from rfl)).symm)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_product_x5f_integer_x2f_statement_x2e_lit
