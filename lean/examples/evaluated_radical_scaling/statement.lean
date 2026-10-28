import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_scaling_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_11 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (12 : ℂ) Litex.R (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (12 : ℂ) (12 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num)) = (12 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (2 : ℂ) Litex.C (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.numberInC (2 : ℂ))) (let _litex_sqrt := _wd_1_1;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member)))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.R (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (4 : ℂ) Litex.C (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) (Litex.numberInC (4 : ℂ))) (let _litex_sqrt := _wd_1_1;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (12 : ℂ) Litex.R (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (12 : ℂ) (12 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num)) = (12 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.mul _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (2 : ℂ) Litex.C (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.numberInC (2 : ℂ))) (let _litex_sqrt := _wd_1_1;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member)));
        let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.R (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.mul _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (4 : ℂ) Litex.C (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) (Litex.numberInC (4 : ℂ))) (let _litex_sqrt := _wd_1_1;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.denote _equal_wd_1_0 = (M.mulValue (M.number (2 : ℂ)) (Litex.sqrtValue (M := M) (M.number (12 : ℂ)))) from congrArg₂ M.mulValue (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl) (show Litex.denote (_equal_wd_1_0).val.right = (Litex.sqrtValue (M := M) (M.number (12 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (12 : ℂ)) = (M.number (12 : ℂ)) from rfl)))).trans (((Eq.refl (M.mulValue (M.number (2 : ℂ)) (Litex.sqrtValue (M := M) (M.number (12 : ℂ)))))).trans ((((congrArg₂ M.mulValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (12 : ℂ) = (((12 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (12 : ℝ))))).trans (M.mul_numbers (2 : ℂ) ((Real.sqrt (12 : ℝ) : ℝ) : ℂ)))).trans ((congrArg M.number (by
          have _litex_radical_0 : Real.sqrt (12 : ℝ) = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
            apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [_litex_radical_0]
          push_cast
          ring : ((2 : ℂ) * ((Real.sqrt (12 : ℝ) : ℝ) : ℂ)) = ((4 : ℂ) * ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)))).trans ((((congrArg₂ M.mulValue (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (3 : ℝ))))).trans (M.mul_numbers (4 : ℂ) ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)))).symm.trans ((show Litex.denote _equal_wd_1_1 = (M.mulValue (M.number (4 : ℂ)) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) from congrArg₂ M.mulValue (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl) (show Litex.denote (_equal_wd_1_1).val.right = (Litex.sqrtValue (M := M) (M.number (3 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)))).symm)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_scaling_x2f_statement_x2e_lit
