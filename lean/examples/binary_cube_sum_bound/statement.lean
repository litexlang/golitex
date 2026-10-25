import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_cube_x5f_sum_x5f_bound_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_14 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (by
  have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).1
        )
    )
  have h_11 : Litex.In _value_i2 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).1
        )
    )
  have h_15 : Litex.In _value_i3 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_14).1
        )
    )
  exact Litex.Le (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i2 h_11));
  let _wd_1_1 := _value_i3;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i2 h_11))) (Litex.integerToComplex _wd_1_1 h_15))) (Litex.number (M := M) (3 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_14
          have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).1
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).2.1
                )
            )
          have h_9 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_6).2.2
                )
            )
          have h_11 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).1
                )
            )
          have h_12 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).2.1
                )
            )
          have h_13 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_10).2.2
                )
            )
          have h_15 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_14).1
                )
            )
          have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_14).2.1
                )
            )
          have h_17 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_14).2.2
                )
            )
          change (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_6
            have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_10
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_14
                    have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                    rcases _enumerated_values with _enumerated_value | _enumerated_value
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                      exact (by
                        have h_832 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_833 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_832).1
                              )
                          )
                        have h_834 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_832).2.1
                              )
                          )
                        have h_835 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_832).2.2
                              )
                          )
                        have h_836 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_837 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_836).1
                              )
                          )
                        have h_838 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_836).2.1
                              )
                          )
                        have h_839 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_836).2.2
                              )
                          )
                        have h_840 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_841 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_840).1
                              )
                          )
                        have h_842 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_840).2.1
                              )
                          )
                        have h_843 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_840).2.2
                              )
                          )
                        have h_844 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_845 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_846 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w9 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_833) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_844).trans (h_845).symm) (show @Eq M.Value _ _ from Eq.refl _) h_833)));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_833) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_844).trans (h_845).symm) (show @Eq M.Value _ _ from Eq.refl _) h_833)))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_844).trans (h_846).symm) (show @Eq M.Value _ _ from Eq.refl _) h_833))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w9
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w9
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_844 h_845) h_846)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_26971 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_27282 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_26971)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_26971)
                      )
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                      exact (by
                        have h_27353 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_27354 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_27353).1
                              )
                          )
                        have h_27355 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_27353).2.1
                              )
                          )
                        have h_27356 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_27353).2.2
                              )
                          )
                        have h_27357 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_27358 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27357).1
                              )
                          )
                        have h_27359 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27357).2.1
                              )
                          )
                        have h_27360 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27357).2.2
                              )
                          )
                        have h_27361 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_27362 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_27361).1
                              )
                          )
                        have h_27363 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_27361).2.1
                              )
                          )
                        have h_27364 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_27361).2.2
                              )
                          )
                        have h_27365 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_27366 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_27367 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w18 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_27354) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_27365).trans (h_27366).symm) (show @Eq M.Value _ _ from Eq.refl _) h_27354)));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_27354) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_27365).trans (h_27366).symm) (show @Eq M.Value _ _ from Eq.refl _) h_27354)))) (Litex.integerToComplex _wd_1_1 h_27362)))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w18
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w18
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_27365 h_27366) h_27367)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_50103 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_50366 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_50103)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_50103)
                      )
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_14
                    have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                    rcases _enumerated_values with _enumerated_value | _enumerated_value
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                      exact (by
                        have h_50433 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_50434 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_50433).1
                              )
                          )
                        have h_50435 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_50433).2.1
                              )
                          )
                        have h_50436 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_50433).2.2
                              )
                          )
                        have h_50437 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_50438 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_50437).1
                              )
                          )
                        have h_50439 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_50437).2.1
                              )
                          )
                        have h_50440 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_50437).2.2
                              )
                          )
                        have h_50441 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_50442 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_50441).1
                              )
                          )
                        have h_50443 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_50441).2.1
                              )
                          )
                        have h_50444 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_50441).2.2
                              )
                          )
                        have h_50445 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_50446 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_50447 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w27 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_50434) (Litex.integerToComplex _value_i2 h_50438));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_50434) (Litex.integerToComplex _value_i2 h_50438))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_50445).trans (h_50447).symm) (show @Eq M.Value _ _ from Eq.refl _) h_50434))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w27
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w27
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_50445 h_50446) h_50447)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_72262 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_72517 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_72262)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_72262)
                      )
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                      exact (by
                        have h_72584 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_72585 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_72584).1
                              )
                          )
                        have h_72586 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_72584).2.1
                              )
                          )
                        have h_72587 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_72584).2.2
                              )
                          )
                        have h_72588 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_72589 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_72588).1
                              )
                          )
                        have h_72590 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_72588).2.1
                              )
                          )
                        have h_72591 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_72588).2.2
                              )
                          )
                        have h_72592 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_72593 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_72592).1
                              )
                          )
                        have h_72594 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_72592).2.1
                              )
                          )
                        have h_72595 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_72592).2.2
                              )
                          )
                        have h_72596 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_72597 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_72598 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w36 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_72585) (Litex.integerToComplex _value_i2 h_72589));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_72585) (Litex.integerToComplex _value_i2 h_72589))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i2 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_72597).trans (h_72598).symm) (show @Eq M.Value _ _ from Eq.refl _) h_72589))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w36
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w36
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_72596 h_72597) h_72598)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_94344 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_94599 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) + (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_94344)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_94344)
                      )
                  )
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_10
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_14
                    have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                    rcases _enumerated_values with _enumerated_value | _enumerated_value
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                      exact (by
                        have h_94662 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_94663 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_94662).1
                              )
                          )
                        have h_94664 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_94662).2.1
                              )
                          )
                        have h_94665 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_94662).2.2
                              )
                          )
                        have h_94666 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_94667 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_94666).1
                              )
                          )
                        have h_94668 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_94666).2.1
                              )
                          )
                        have h_94669 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_94666).2.2
                              )
                          )
                        have h_94670 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_94671 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_94670).1
                              )
                          )
                        have h_94672 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_94670).2.1
                              )
                          )
                        have h_94673 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_94670).2.2
                              )
                          )
                        have h_94674 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_94675 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_94676 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w45 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_94663) (Litex.integerToComplex _value_i2 h_94667));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_94663) (Litex.integerToComplex _value_i2 h_94667))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i2 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_94675).trans (h_94676).symm) (show @Eq M.Value _ _ from Eq.refl _) h_94667))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w45
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w45
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_94674 h_94675) h_94676)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_116497 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_116752 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (0 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_116497)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_116497)
                      )
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                      exact (by
                        have h_116819 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_116820 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_116819).1
                              )
                          )
                        have h_116821 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_116819).2.1
                              )
                          )
                        have h_116822 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_116819).2.2
                              )
                          )
                        have h_116823 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_116824 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_116823).1
                              )
                          )
                        have h_116825 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_116823).2.1
                              )
                          )
                        have h_116826 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_116823).2.2
                              )
                          )
                        have h_116827 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_116828 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_116827).1
                              )
                          )
                        have h_116829 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_116827).2.1
                              )
                          )
                        have h_116830 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_116827).2.2
                              )
                          )
                        have h_116831 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_116832 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_116833 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w54 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_116820) (Litex.integerToComplex _value_i2 h_116824));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_116820) (Litex.integerToComplex _value_i2 h_116824))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_116831).trans (h_116833).symm) (show @Eq M.Value _ _ from Eq.refl _) h_116820))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w54
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w54
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_116831 h_116832) h_116833)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_138581 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_138836 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (0 : ℂ)) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_138581)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (0 : ℂ))) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_138581)
                      )
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_14
                    have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                    rcases _enumerated_values with _enumerated_value | _enumerated_value
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                      exact (by
                        have h_138899 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_138900 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_138899).1
                              )
                          )
                        have h_138901 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_138899).2.1
                              )
                          )
                        have h_138902 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_138899).2.2
                              )
                          )
                        have h_138903 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_138904 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_138903).1
                              )
                          )
                        have h_138905 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_138903).2.1
                              )
                          )
                        have h_138906 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_138903).2.2
                              )
                          )
                        have h_138907 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_138908 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_138907).1
                              )
                          )
                        have h_138909 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_138907).2.1
                              )
                          )
                        have h_138910 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_138907).2.2
                              )
                          )
                        have h_138911 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_138912 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_138913 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w63 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_138900) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_138911).trans (h_138912).symm) (show @Eq M.Value _ _ from Eq.refl _) h_138900)));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_138900) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_138911).trans (h_138912).symm) (show @Eq M.Value _ _ from Eq.refl _) h_138900)))) (Litex.integerToComplex _wd_1_1 h_138908)))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w63
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w63
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_138911 h_138912) h_138913)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_161610 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_161873 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (0 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (0 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_161610)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_161610)
                      )
                    · have _enumerated_case_2 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                      exact (by
                        have h_161936 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_6
                              )
                          )
                        have h_161937 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_161936).1
                              )
                          )
                        have h_161938 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_161936).2.1
                              )
                          )
                        have h_161939 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i1 h_161936).2.2
                              )
                          )
                        have h_161940 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_10
                              )
                          )
                        have h_161941 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_161940).1
                              )
                          )
                        have h_161942 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_161940).2.1
                              )
                          )
                        have h_161943 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_161940).2.2
                              )
                          )
                        have h_161944 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                h_14
                              )
                          )
                        have h_161945 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_161944).1
                              )
                          )
                        have h_161946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_161944).2.1
                              )
                          )
                        have h_161947 : Litex.Lt _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_161944).2.2
                              )
                          )
                        have h_161948 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_0
                              )
                          )
                        have h_161949 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_1
                              )
                          )
                        have h_161950 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                _enumerated_case_2
                              )
                          )
                        let _object_w72 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_161937) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_161948).trans (h_161949).symm) (show @Eq M.Value _ _ from Eq.refl _) h_161937)));
                        let _wd_1_1 := _value_i3;
                        (Litex.add _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.addInC _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_161937) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_161948).trans (h_161949).symm) (show @Eq M.Value _ _ from Eq.refl _) h_161937)))) (Litex.integerToComplex _wd_1_1 (Litex.inOfSame _value_i1 _wd_1_1 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_161948).trans (h_161950).symm) (show @Eq M.Value _ _ from Eq.refl _) h_161937))))

                        have h_3 : (by
                          let _atomic_wd_1_0 := _object_w72
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := _object_w72
                                  exact (Litex.leOfSame (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.addValue h_161948 h_161949) h_161950)).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (by
                                    let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                    (Litex.add _wd_1_0 _wd_1_1 (by
                                      let _atomic_wd_3_0 := _wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                      let _atomic_wd_3_0 := _atomic_wd_2_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                              )
                          )
                        have h_187890 : (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                          (Litex.add _wd_1_0 _wd_1_1 (by
                            let _atomic_wd_2_0 := _wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                          exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_2_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                              )
                          )
                        have h_188201 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (by
                                  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                                  (Litex.add _wd_1_0 _wd_1_1 (by
                                    let _atomic_wd_1_0 := _wd_1_0
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))
                                  exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).mpr (by
                                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                      apply Complex.ofReal_injective
                                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                    let _atomic_wd_2_0 := _atomic_wd_1_1
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (1 : ℂ)) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (1 : ℂ)) (by
                                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_187890)
                              )
                          )
                        show (∃ (_r _s : ℝ), (M.addValue (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                        exact Eq.mpr (Eq.trans (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue _enumeration_value (Litex.denote _value_i2)) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) _enumeration_value) (Litex.denote _value_i3)) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_2)) (show (∃ (_r _s : ℝ), (M.addValue (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_187890)
                      )
                  )
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_binary_x5f_cube_x5f_sum_x5f_bound_x2f_statement_x2e_lit
