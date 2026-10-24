import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_singleton_x5f_integer_x5f_range_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5
          have h_6 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5).1
                )
            )
          have h_7 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5).2.1
                )
            )
          have h_8 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_5).2.2
                )
            )
          have h_9 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (by norm_num) h_5)
                )
            )
          have h_10 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨k, hk, hlo, hhi⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (2 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_5
                    have heq : k = (2 : ℤ) := by omega
                    exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (2 : ℂ))).trans ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).symm)
                  )
                )
            )
          have h_13 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_13).1
                )
            )
          have h_15 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_13).2.1
                )
            )
          have h_16 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_13).2.2
                )
            )
          have h_17 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (by norm_num) h_13)
                )
            )
          have h_18 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨k, hk, hlo, hhi⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (2 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_13
                    have heq : k = (2 : ℤ) := by omega
                    exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (2 : ℂ))).trans ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).symm)
                  )
                )
            )
          have h_25 : (Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _expanded_range := (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.inRangeInteger _expanded_range _value_i1 (2 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (by
                      let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                      exact h_13)
                    have _range_cases : _range_integer = (2 : ℤ) := by omega
                    exact (_range_same.trans (congrArg M.number (by norm_num [_range_cases])))
                  )
                )
            )
          exact h_18
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_singleton_x5f_integer_x5f_range_x2f_statement_x2e_lit
