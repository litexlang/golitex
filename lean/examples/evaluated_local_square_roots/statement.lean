import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_square_x5f_roots_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (Litex.number (M := M) (16 : ℂ))
  have h_4 : Litex.In _object_i1 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))
        )
    )
  have h_5 : Litex.Same _object_i1 (Litex.number (M := M) (16 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.number (M := M) (16 : ℂ)))
        )
    )
  have h_262 : (by
    let _equal_wd_1_0 := (Litex.sqrt _object_i1 h_4 (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) _object_i1 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_5).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4) = (16 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.sqrt _object_i1 h_4 (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) _object_i1 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_5).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4) = (16 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.sqrtValue (M := M) (Litex.denote _object_i1)) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl)) (((congrArg (Litex.sqrtValue (M := M)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl)) h_5) (show Litex.denote (Litex.number (M := M) (16 : ℂ)) = (M.number (16 : ℂ)) from rfl)))).trans (show (Litex.sqrtValue (M := M) (M.number (16 : ℂ))) = M.number (4 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.number (16 : ℂ)) = M.number (16 : ℂ) from (congrArg M.number (show (16 : ℂ) = (16 : ℂ) from by norm_num)))).trans (by
            have _argument : (16 : ℂ) = (((16 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (16 : ℝ) = (4 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((4 : ℝ) : ℝ) : ℂ) = (4 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (16 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))).symm)))
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (Litex.sqrt _object_i1 h_4 (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) _object_i1 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_5).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4) = (16 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.inOfSame _object_i1 (Litex.number (M := M) (16 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_5 (show @Eq M.Value _ _ from Eq.refl _) h_4)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_262
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_square_x5f_roots_x2f_statement_x2e_lit
