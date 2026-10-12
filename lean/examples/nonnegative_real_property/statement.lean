import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonnegative_x5f_real_x5f_property_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1

theorem h_41 : ((prop_1 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num))) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num))))

theorem h_46 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
  (by rcases (h_41 (M := M)) with ⟨h_2, h_1⟩; exact h_2)

theorem h_47 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by rcases (h_41 (M := M)) with ⟨h_2, h_1⟩; exact h_1)

theorem h_56 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num))) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num))) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (0 : ℂ) (0 : ℝ) (by norm_num)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by rcases (h_41 (M := M)) with ⟨h_2, h_1⟩; exact h_1))

theorem h_71 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) (h_56 (M := M)))

theorem h_85 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_100 : Litex.In _value_i3 (Litex.R (M := M))) (h_83 : ((prop_1 (M := M)) _value_i3)), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_100 h_83
    have h_102 : Litex.In _value_i3 (Litex.R (M := M)) :=
      (by rcases h_83 with ⟨h_2, h_1⟩; exact h_2)
    have h_105 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by rcases h_83 with ⟨h_2, h_1⟩; exact h_1)
    have h_84 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      h_105
    exact h_84
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonnegative_x5f_real_x5f_property_x2f_statement_x2e_lit
