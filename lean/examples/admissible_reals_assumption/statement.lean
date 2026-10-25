import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_admissible_x5f_reals_x5f_assumption_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 1 → M.Value) → Prop)

variable (h_4 : (∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (abstract_prop_1 ![(Litex.denote _value_i3)])), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))

theorem h_3 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_4 : (∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (abstract_prop_1 ![(Litex.denote _value_i3)])), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_5 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (abstract_prop_1 ![(Litex.denote _value_i3)])), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_5 h_1
          have h_14 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_4 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 := (@h_4 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_14 h_1)
          exact (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _value_i3 h_4)
        )
      )
  )

variable (h_45 : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (2 : ℂ)))]))

theorem h_46 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_4 : (∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (abstract_prop_1 ![(Litex.denote _value_i3)])), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (h_45 : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (2 : ℂ)))])) : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_47 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_48 : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (2 : ℂ)))]) :=
            (by
              litex_checked_step =>
                exact (
                  h_45
                )
            )
          have h_49 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (((h_3 (M := M) abstract_prop_1) (h_4 := h_4)) (Litex.number (M := M) (2 : ℂ)) h_47 h_48)
                )
            )
          have h_60 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_49)
                )
            )
          exact h_49
        )
      )
  )

theorem h_77 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_4 : (∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_14 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (abstract_prop_1 ![(Litex.denote _value_i3)])), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (h_45 : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (2 : ℂ)))])) : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (h_46 (M := M) abstract_prop_1 (h_4 := h_4) (h_45 := h_45)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_admissible_x5f_reals_x5f_assumption_x2f_statement_x2e_lit
