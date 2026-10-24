import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_square_x5f_root_x5f_sum_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (let _wd_1_0 := (Litex.sqrt (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((let _litex_sqrt := _atomic_wd_1_0;
  let _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;
  (Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 (4 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by have _sqrt_value : Real.sqrt (4 : ℝ) = (2 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num); rw [_sqrt_value]; norm_num : ((Real.sqrt (4 : ℝ) : ℝ) : ℂ) = (2 : ℂ))))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_w2 := ((_object_w1 (M := M))).val.left

theorem h_12 : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_square_x5f_root_x5f_sum_x2f_statement_x2e_lit
