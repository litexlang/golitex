import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_square_x5f_roots_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (9 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (9 : ℂ)))
      )
  )

theorem h_261 : (by
  let _equal_wd_1_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (9 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (9 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (((congrArg (Litex.sqrtValue (M := M)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (9 : ℂ)) = (M.number (9 : ℂ)) from rfl)))).trans (show (Litex.sqrtValue (M := M) (M.number (9 : ℂ))) = M.number (3 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans (by
          have _argument : (9 : ℂ) = (((9 : ℝ) : ℝ) : ℂ) := by norm_num
          have _root : Real.sqrt (9 : ℝ) = (3 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
          have _cast : (((3 : ℝ) : ℝ) : ℂ) = (3 : ℂ) := by norm_num
          exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (9 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))).symm)))
      )
  )

theorem h_518 : (by
  let _equal_wd_1_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (9 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (9 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_261 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_square_x5f_roots_x2f_statement_x2e_lit
