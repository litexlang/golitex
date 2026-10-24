import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_set_x5f_membership_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_3 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_4 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_3).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_3 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_3).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
                )
            )
          exact (by
          let _set := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))
          exact (Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) _set.val.bound _set.val.predicate).mpr ⟨h_3, h_4⟩)
        )
      )
  )

theorem h_36 : (M.mem (M.number (1 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))) (h_2 (M := M))))).choose
      )
  )

theorem h_37 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))) (h_2 (M := M))))).choose_spec
      )
  )

theorem h_40 : (by
  let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))
  exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_42 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_43 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_42).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) h_42 = (2 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) h_42).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
                )
            )
          have h_41 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_62 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _set := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_62 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))
                    exact (Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) _set.val.bound _set.val.predicate).mpr ⟨h_42, h_43⟩)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))
          exact (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_62 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (show Litex.Same (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_62 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) _atomic_wd_1_1 from rfl) h_41))
        )
      )
  )

theorem h_124 : (M.mem (M.number (2 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))) (h_40 (M := M))))).choose
      )
  )

theorem h_125 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_108 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3))) (h_40 (M := M))))).choose_spec
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_set_x5f_membership_x2f_statement_x2e_lit
