import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_rectangle_x5f_bound_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (by
  have h_9 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8).1
        )
    )
  have h_23 : Litex.In _value_i2 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22).1
        )
    )
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_9) (Litex.integerToComplex _value_i1 h_9));
    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_23) (Litex.integerToComplex _value_i2 h_23));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_9) (Litex.integerToComplex _value_i1 h_9))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_23) (Litex.integerToComplex _value_i2 h_23)))))
    exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_22
          have h_9 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8).1
                )
            )
          have h_10 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8).2.1
                )
            )
          have h_11 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_8).2.2
                )
            )
          have h_23 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22).1
                )
            )
          have h_24 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22).2.1
                )
            )
          have h_25 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_22).2.2
                )
            )
          have h_1127 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_1141 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_1128 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1127).1
                )
            )
          have h_1129 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1127).2.1
                )
            )
          have h_1130 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1127).2.2
                )
            )
          have h_1142 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1141).1
                )
            )
          have h_1143 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1141).2.1
                )
            )
          have h_1144 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1141).2.2
                )
            )
          have h_4 : ∀ (_enumerated_i3 : M.Value) (h_1145 : M.mem _enumerated_i3 (Litex.denote (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))) (_enumerated_i4 : M.Value) (h_1149 : M.mem _enumerated_i4 (Litex.denote (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))), (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumerated_i3 _enumerated_i3) (M.mulValue _enumerated_i4 _enumerated_i4)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _enumerated_i3 h_1145 _enumerated_i4 h_1149
                    let _value_i3 := Litex.semanticObject _enumerated_i3 (M.member_isSet h_1145)
                    let _value_i4 := Litex.semanticObject _enumerated_i4 (M.member_isSet h_1149)
                    have h_1146 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_1145).1
                          )
                      )
                    have h_1147 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_1145).2.1
                          )
                      )
                    have h_1148 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_1145).2.2
                          )
                      )
                    have h_1150 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_1149).1
                          )
                      )
                    have h_1151 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_1149).2.1
                          )
                      )
                    have h_1152 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_1149).2.2
                          )
                      )
                    change (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact (by
                      obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_1145
                      have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
                      rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_1149
                          have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                            exact (by
                              have h_2710 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_2711 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_2710).1
                                    )
                                )
                              have h_2712 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_2710).2.1
                                    )
                                )
                              have h_2713 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_2710).2.2
                                    )
                                )
                              have h_2714 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_2715 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_2714).1
                                    )
                                )
                              have h_2716 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_2714).2.1
                                    )
                                )
                              have h_2717 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_2714).2.2
                                    )
                                )
                              have h_2718 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_2719 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w13 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_2711) (Litex.integerToComplex _value_i3 h_2711));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_2718).trans (h_2719).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2711)) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_2718).trans (h_2719).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2711)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_2711) (Litex.integerToComplex _value_i3 h_2711))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_2718).trans (h_2719).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2711)) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_2718).trans (h_2719).symm) (show @Eq M.Value _ _ from Eq.refl _) h_2711))))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w13
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w13
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_2718 h_2718) (congrArg₂ M.mulValue h_2719 h_2719))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                          let _wd_1_1 := _wd_1_0;
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.left (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_37818 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := _wd_1_0;
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_38331 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                      let _wd_1_1 := _wd_1_0;
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_37818)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_37818)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_38412 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_38413 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_38412).1
                                    )
                                )
                              have h_38414 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_38412).2.1
                                    )
                                )
                              have h_38415 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_38412).2.2
                                    )
                                )
                              have h_38416 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_38417 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_38416).1
                                    )
                                )
                              have h_38418 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_38416).2.1
                                    )
                                )
                              have h_38419 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_38416).2.2
                                    )
                                )
                              have h_38420 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_38421 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w18 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_38413) (Litex.integerToComplex _value_i3 h_38413));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_38417) (Litex.integerToComplex _value_i4 h_38417));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_38413) (Litex.integerToComplex _value_i3 h_38413))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_38417) (Litex.integerToComplex _value_i4 h_38417)))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w18
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w18
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_38420 h_38420) (congrArg₂ M.mulValue h_38421 h_38421))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.right
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_69455 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_69904 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((0 : ℂ) * (0 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_69455)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_69455)
                            )
                        )
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_1149
                          have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                            exact (by
                              have h_69981 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_69982 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_69981).1
                                    )
                                )
                              have h_69983 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_69981).2.1
                                    )
                                )
                              have h_69984 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_69981).2.2
                                    )
                                )
                              have h_69985 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_69986 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_69985).1
                                    )
                                )
                              have h_69987 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_69985).2.1
                                    )
                                )
                              have h_69988 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_69985).2.2
                                    )
                                )
                              have h_69989 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_69990 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w23 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_69982) (Litex.integerToComplex _value_i3 h_69982));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_69986) (Litex.integerToComplex _value_i4 h_69986));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_69982) (Litex.integerToComplex _value_i3 h_69982))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_69986) (Litex.integerToComplex _value_i4 h_69986)))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w23
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w23
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_69989 h_69989) (congrArg₂ M.mulValue h_69990 h_69990))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.right
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_101024 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_101473 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_101024)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_101024)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_101550 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_101551 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_101550).1
                                    )
                                )
                              have h_101552 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_101550).2.1
                                    )
                                )
                              have h_101553 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_101550).2.2
                                    )
                                )
                              have h_101554 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_101555 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_101554).1
                                    )
                                )
                              have h_101556 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_101554).2.1
                                    )
                                )
                              have h_101557 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_101554).2.2
                                    )
                                )
                              have h_101558 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_101559 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w28 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_101551) (Litex.integerToComplex _value_i3 h_101551));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_101558).trans (h_101559).symm) (show @Eq M.Value _ _ from Eq.refl _) h_101551)) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_101558).trans (h_101559).symm) (show @Eq M.Value _ _ from Eq.refl _) h_101551)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_101551) (Litex.integerToComplex _value_i3 h_101551))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_101558).trans (h_101559).symm) (show @Eq M.Value _ _ from Eq.refl _) h_101551)) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_101558).trans (h_101559).symm) (show @Eq M.Value _ _ from Eq.refl _) h_101551))))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w28
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w28
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_101558 h_101558) (congrArg₂ M.mulValue h_101559 h_101559))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                          let _wd_1_1 := _wd_1_0;
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.left (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_136672 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                let _wd_1_1 := _wd_1_0;
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_137185 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                      let _wd_1_1 := _wd_1_0;
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        let _wd_1_1 := _wd_1_0;
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) * (1 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_136672)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_136672)
                            )
                        )
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_1149
                          have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                            exact (by
                              have h_137258 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_137259 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_137258).1
                                    )
                                )
                              have h_137260 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_137258).2.1
                                    )
                                )
                              have h_137261 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_137258).2.2
                                    )
                                )
                              have h_137262 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_137263 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_137262).1
                                    )
                                )
                              have h_137264 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_137262).2.1
                                    )
                                )
                              have h_137265 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_137262).2.2
                                    )
                                )
                              have h_137266 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_137267 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w32 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_137259) (Litex.integerToComplex _value_i3 h_137259));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_137263) (Litex.integerToComplex _value_i4 h_137263));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_137259) (Litex.integerToComplex _value_i3 h_137259))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_137263) (Litex.integerToComplex _value_i4 h_137263)))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w32
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w32
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_137266 h_137266) (congrArg₂ M.mulValue h_137267 h_137267))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.right
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_168349 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_168798 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((0 : ℂ) * (0 : ℂ))) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_168349)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_168349)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_168875 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1145
                                    )
                                )
                              have h_168876 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_168875).1
                                    )
                                )
                              have h_168877 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_168875).2.1
                                    )
                                )
                              have h_168878 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_168875).2.2
                                    )
                                )
                              have h_168879 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_1149
                                    )
                                )
                              have h_168880 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_168879).1
                                    )
                                )
                              have h_168881 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_168879).2.1
                                    )
                                )
                              have h_168882 : Litex.Lt _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_168879).2.2
                                    )
                                )
                              have h_168883 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_168884 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w37 := (let _wd_1_0 := (Litex.mul _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_168876) (Litex.integerToComplex _value_i3 h_168876));
                              let _wd_1_1 := (Litex.mul _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_168880) (Litex.integerToComplex _value_i4 h_168880));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.mulInC _value_i3 _value_i3 (Litex.integerToComplex _value_i3 h_168876) (Litex.integerToComplex _value_i3 h_168876))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.mulInC _value_i4 _value_i4 (Litex.integerToComplex _value_i4 h_168880) (Litex.integerToComplex _value_i4 h_168880)))))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w37
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w37
                                        exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_168883 h_168883) (congrArg₂ M.mulValue h_168884 h_168884))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
                                          let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                          (Litex.add _wd_1_0 _wd_1_1 (by
                                            let _atomic_wd_3_0 := _wd_1_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_3_0 := _wd_1_1
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_3_0).val.left (_atomic_wd_3_0).val.right (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_3_0).val.left).wd.1 ((_atomic_wd_3_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_3_0).val.right).wd.1 ((_atomic_wd_3_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.left
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_3_0 := (_atomic_wd_2_0).val.right
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_199973 : (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                (Litex.add _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_2_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_2_0).val.left).wd.1 ((_atomic_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_2_0).val.right).wd.1 ((_atomic_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_200422 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                      let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                      (Litex.add _wd_1_0 _wd_1_1 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                        let _atomic_wd_1_0 := _wd_1_1
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                                        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                                        (Litex.add _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_1_0 := _wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_199973)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i3) (Litex.denote _value_i3)) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_199973)
                            )
                        )
                    )
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1128) (Litex.integerToComplex _value_i1 h_1128));
            let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_1142) (Litex.integerToComplex _value_i2 h_1142));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1128) (Litex.integerToComplex _value_i1 h_1128))) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_1142) (Litex.integerToComplex _value_i2 h_1142)))))
            exact (by
              have h_222891 : (by
                let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                exact Litex.In _value_i1 _atomic_wd_2_1) :=
                (by
                  let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                  exact h_1127)
              have h_222896 : (by
                let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                exact Litex.In _value_i2 _atomic_wd_2_1) :=
                (by
                  let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                  exact h_1141)
              exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (congrArg₂ M.addValue (congrArg₂ M.mulValue (Litex.sameRefl _value_i1) (Litex.sameRefl _value_i1)) (congrArg₂ M.mulValue (Litex.sameRefl _value_i2) (Litex.sameRefl _value_i2))) (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) ((fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) h_1145 {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) h_1149 => h_4 (Litex.denote _value_i3) h_1145 (Litex.denote _value_i4) h_1149) _value_i1 h_222891 _value_i2 h_222896))
            ))
        )
      )
  )

theorem h_224024 : (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_224025 : (by
            let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    exact (Litex.numberInRangeOfEq (M := M) (0 : ℂ) (3 : ℂ) (2 : ℂ) (0 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
                )
            )
          have h_224030 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_224025).1
                )
            )
          have h_224031 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_224025).2.1
                )
            )
          have h_224032 : Litex.Lt (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_224025).2.2
                )
            )
          have h_224026 : (by
            let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_224030)
            exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_224030)
                    exact (Litex.numberInRangeOfEq (M := M) (0 : ℂ) (2 : ℂ) (1 : ℂ) (0 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
                )
            )
          have h_224051 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_224030) (Litex.number (M := M) (1 : ℂ)) h_224026).1
                )
            )
          have h_224052 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_224030) (Litex.number (M := M) (1 : ℂ)) h_224026).2.1
                )
            )
          have h_224053 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_224030) (Litex.number (M := M) (1 : ℂ)) h_224026).2.2
                )
            )
          have h_224027 : Litex.Le (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_224025 (Litex.number (M := M) (1 : ℂ)) h_224026)
                )
            )
          have h_224318 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.add _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                    let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                        let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
                      let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                      let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_224027)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
          exact h_224027)
        )
      )
  )

theorem h_224383 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
              let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((2 : ℂ) * (2 : ℂ)) + ((1 : ℂ) * (1 : ℂ))) (5 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_224024 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_rectangle_x5f_bound_x2f_statement_x2e_lit
