import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_half_x5f_open_x5f_integer_x5f_range_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), ((Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7
          have h_8 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7).1
                )
            )
          have h_9 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7).2.1
                )
            )
          have h_10 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_7).2.2
                )
            )
          have h_11 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7)
                )
            )
          have h_14 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_14).1
                )
            )
          have h_16 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_14).2.1
                )
            )
          have h_17 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_14).2.2
                )
            )
          have h_18 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_14)
                )
            )
          have h_26 : (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _expanded_range := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.inRangeInteger _expanded_range _value_i1 (1 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (by
                      let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                      exact h_14)
                    have _range_cases : _range_integer = (1 : ℤ) ∨ _range_integer = (2 : ℤ) := by omega
                    rcases _range_cases with _range_case | _range_case
                    · exact (Or.inl (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                    · exact (Or.inr (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                  )
                )
            )
          exact h_26
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_half_x5f_open_x5f_integer_x5f_range_x2f_statement_x2e_lit
