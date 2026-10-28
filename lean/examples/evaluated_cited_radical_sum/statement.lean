import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_radical_x5f_sum_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (12 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (12 : ℂ) (12 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (12 : ℂ)))
      )
  )

theorem h_549 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (12 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) = (27 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (27 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (5 : ℂ));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (5 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (12 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (12 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (12 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (12 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num)) = (27 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (27 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (27 : ℂ) (27 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (27 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        let _equal_wd_1_1 := (let _wd_1_0 := (Litex.number (M := M) (5 : ℂ));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (5 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.denote _equal_wd_1_0 = (M.addValue (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) (Litex.sqrtValue (M := M) (M.number (27 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_0).val.left = (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (show Litex.denote (_equal_wd_1_0).val.right = (Litex.sqrtValue (M := M) (M.number (27 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (27 : ℂ)) = (M.number (27 : ℂ)) from rfl)))).trans (((congrArg₂ M.addValue (congrArg (Litex.sqrtValue (M := M)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (12 : ℂ)) = (M.number (12 : ℂ)) from rfl))) (Eq.refl (Litex.sqrtValue (M := M) (M.number (27 : ℂ)))))).trans ((((congrArg₂ M.addValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (12 : ℂ)) = M.number (12 : ℂ) from (congrArg M.number (show (12 : ℂ) = (12 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (12 : ℂ) = (((12 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (12 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (27 : ℂ)) = M.number (27 : ℂ) from (congrArg M.number (show (27 : ℂ) = (27 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (27 : ℂ) = (((27 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (27 : ℝ))))).trans (M.add_numbers ((Real.sqrt (12 : ℝ) : ℝ) : ℂ) ((Real.sqrt (27 : ℝ) : ℝ) : ℂ)))).trans ((congrArg M.number (by
          have _litex_radical_0 : Real.sqrt (12 : ℝ) = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
            apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          have _litex_radical_1 : Real.sqrt (27 : ℝ) = (3 : ℝ) * Real.sqrt (3 : ℝ) := by
            apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [_litex_radical_0, _litex_radical_1]
          push_cast
          ring : (((Real.sqrt (12 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (27 : ℝ) : ℝ) : ℂ)) = ((5 : ℂ) * ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)))).trans ((((congrArg₂ M.mulValue (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (3 : ℝ))))).trans (M.mul_numbers (5 : ℂ) ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)))).symm.trans ((show Litex.denote _equal_wd_1_1 = (M.mulValue (M.number (5 : ℂ)) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) from congrArg₂ M.mulValue (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl) (show Litex.denote (_equal_wd_1_1).val.right = (Litex.sqrtValue (M := M) (M.number (3 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)))).symm)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_radical_x5f_sum_x2f_statement_x2e_lit
