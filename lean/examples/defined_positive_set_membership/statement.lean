import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_positive_x5f_set_x5f_membership_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))
theorem h_11 : Litex.Same (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) :=
  (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)))

theorem h_12 : Litex.In (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) :=
  (by
    have h_12 : Litex.In (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M)))).symm (by
              let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))
              exact (by
                let _set := _atomic_wd_2_1
                exact (Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) _set.val.bound _set.val.predicate).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))⟩)))
          )
      )
    have h_18 : (M.mem (M.number (1 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) h_12))).choose
          )
      )
    have h_19 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) h_12))).choose_spec
          )
      )
    exact h_12
  )

theorem h_22 : (M.mem (M.number (1 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
  (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) (h_12 (M := M))))).choose

theorem h_23 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (((Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) (h_12 (M := M))))).choose_spec

theorem h_24 : Litex.In (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) :=
  (by
    have h_25 : Litex.In (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M)))).symm (by
              let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))
              exact (by
                let _set := _atomic_wd_2_1
                exact (Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) _set.val.bound _set.val.predicate).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))⟩)))
          )
      )
    have h_61 : (M.mem (M.number (2 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) h_25))).choose
          )
      )
    have h_62 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) h_25))).choose_spec
          )
      )
    have h_25 : Litex.In (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_25
          )
      )
    exact h_25
  )

theorem h_71 : (M.mem (M.number (2 : ℂ)) (M.standard Litex.StandardSetValue.real)) :=
  (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) (h_24 (M := M))))).choose

theorem h_72 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (((Litex.inSetBuilder_iff (Litex.number (M := M) (2 : ℂ)) ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))).val.predicate).mp (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_11 (M := M))) (h_24 (M := M))))).choose_spec
end LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_positive_x5f_set_x5f_membership_x2f_statement_x2e_lit
