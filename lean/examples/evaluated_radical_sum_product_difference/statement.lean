import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_sum_x5f_product_x5f_difference_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_33 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sqrt (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) Litex.R (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.R (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (let _litex_sqrt := _wd_2_0;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member) (let _litex_sqrt := _wd_2_1;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member)));
  let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.left;
  let _wd_2_1 := (_wd_1_0).val.right;
  (Litex.sub _wd_2_0 _wd_2_1 (let _litex_sqrt := _wd_2_0;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member) (let _litex_sqrt := _wd_2_1;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member)));
  (Litex.mul _wd_1_0 _wd_1_1 (let _litex_closed := (Litex.add (_wd_1_0).val.left (_wd_1_0).val.right (let _litex_sqrt := (_wd_1_0).val.left;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member) (let _litex_sqrt := (_wd_1_0).val.right;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member));
  let _litex_member : Litex.In _litex_closed Litex.C := (Litex.addInC _litex_closed.val.left _litex_closed.val.right _litex_closed.wd.1 _litex_closed.wd.2);
  _litex_member) (let _litex_closed := (Litex.sub (_wd_1_1).val.left (_wd_1_1).val.right (let _litex_sqrt := (_wd_1_1).val.left;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member) (let _litex_sqrt := (_wd_1_1).val.right;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  _litex_sqrt_member));
  let _litex_member : Litex.In _litex_closed Litex.C := (Litex.subInC _litex_closed.val.left _litex_closed.val.right _litex_closed.wd.1 _litex_closed.wd.2);
  _litex_member)))
  let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) Litex.C (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (Litex.numberInC (1 : ℂ))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sqrt (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) Litex.R (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.R (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_2_0 _wd_2_1 (let _litex_sqrt := _wd_2_0;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member) (let _litex_sqrt := _wd_2_1;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member)));
        let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.left;
        let _wd_2_1 := (_wd_1_0).val.right;
        (Litex.sub _wd_2_0 _wd_2_1 (let _litex_sqrt := _wd_2_0;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member) (let _litex_sqrt := _wd_2_1;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member)));
        (Litex.mul _wd_1_0 _wd_1_1 (let _litex_closed := (Litex.add (_wd_1_0).val.left (_wd_1_0).val.right (let _litex_sqrt := (_wd_1_0).val.left;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member) (let _litex_sqrt := (_wd_1_0).val.right;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member));
        let _litex_member : Litex.In _litex_closed Litex.C := (Litex.addInC _litex_closed.val.left _litex_closed.val.right _litex_closed.wd.1 _litex_closed.wd.2);
        _litex_member) (let _litex_closed := (Litex.sub (_wd_1_1).val.left (_wd_1_1).val.right (let _litex_sqrt := (_wd_1_1).val.left;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member) (let _litex_sqrt := (_wd_1_1).val.right;
        let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
        _litex_sqrt_member));
        let _litex_member : Litex.In _litex_closed Litex.C := (Litex.subInC _litex_closed.val.left _litex_closed.val.right _litex_closed.wd.1 _litex_closed.wd.2);
        _litex_member)));
        let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) Litex.C (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (Litex.numberInC (1 : ℂ))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.denote _equal_wd_1_0 = (M.mulValue (M.addValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) (M.subValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ))))) from congrArg₂ M.mulValue (show Litex.denote (_equal_wd_1_0).val.left = (M.addValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote ((_equal_wd_1_0).val.left).val.left = (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)) (show Litex.denote ((_equal_wd_1_0).val.left).val.right = (Litex.sqrtValue (M := M) (M.number (3 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (show Litex.denote (_equal_wd_1_0).val.right = (M.subValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) from congrArg₂ M.subValue (show Litex.denote ((_equal_wd_1_0).val.left).val.left = (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)) (show Litex.denote ((_equal_wd_1_0).val.left).val.right = (Litex.sqrtValue (M := M) (M.number (3 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))).trans (((Eq.refl (M.mulValue (M.addValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) (M.subValue (Litex.sqrtValue (M := M) (M.number (2 : ℂ))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ))))))).trans ((((congrArg₂ M.mulValue ((congrArg₂ M.addValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (2 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (3 : ℝ))))).trans (M.add_numbers ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) ((Real.sqrt (3 : ℝ) : ℝ) : ℂ))) ((congrArg₂ M.subValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (2 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (3 : ℝ))))).trans (M.sub_numbers ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)))).trans (M.mul_numbers (((Real.sqrt (2 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)) (((Real.sqrt (2 : ℝ) : ℝ) : ℂ) - ((Real.sqrt (3 : ℝ) : ℝ) : ℂ))))).trans ((congrArg M.number (by
          have _litex_pair_0 : ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) = (2 : ℂ) := by
            have _litex_product : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = (2 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              norm_num
            exact_mod_cast _litex_product
          have _litex_pair_1 : ((Real.sqrt (3 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (3 : ℝ) : ℝ) : ℂ) = (3 : ℂ) := by
            have _litex_product : Real.sqrt (3 : ℝ) * Real.sqrt (3 : ℝ) = (3 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              norm_num
            exact_mod_cast _litex_product
          linear_combination (1 : ℂ) * _litex_pair_0 + (-1 : ℂ) * _litex_pair_1 : ((((Real.sqrt (2 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)) * (((Real.sqrt (2 : ℝ) : ℝ) : ℂ) - ((Real.sqrt (3 : ℝ) : ℝ) : ℂ))) = (-1 : ℂ))).trans (((show (M.negValue (M.number (1 : ℂ))) = M.number (-1 : ℂ) from ((congrArg M.negValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.neg_numbers (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).symm.trans ((show Litex.denote _equal_wd_1_1 = (M.negValue (M.number (1 : ℂ))) from Eq.trans (((show (M.negValue (M.number (1 : ℂ))) = M.number (-1 : ℂ) from ((congrArg M.negValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.neg_numbers (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))) (Eq.symm (show (M.negValue (M.number (1 : ℂ))) = M.number (-1 : ℂ) from ((congrArg M.negValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.neg_numbers (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).symm)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_radical_x5f_sum_x5f_product_x5f_difference_x2f_statement_x2e_lit
