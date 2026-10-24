import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))), (by
  have h_9 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8).1
        )
    )
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_9) (Litex.integerToComplex _value_i1 h_9))
    exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8
          have h_9 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8).1
                )
            )
          have h_10 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8).2.1
                )
            )
          have h_11 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8).2.2
                )
            )
          have h_204 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_205 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_204).1
                )
            )
          have h_206 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_204).2.1
                )
            )
          have h_207 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_204).2.2
                )
            )
          have h_4 : ∀ (_enumerated_i2 : M.Value) (h_208 : M.mem _enumerated_i2 (Litex.denote (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))))), (∃ (_r _s : ℝ), (M.mulValue _enumerated_i2 _enumerated_i2) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _enumerated_i2 h_208
                    let _value_i2 := Litex.semanticObject _enumerated_i2 (M.member_isSet h_208)
                    have h_209 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_208).1
                          )
                      )
                    have h_210 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_208).2.1
                          )
                      )
                    have h_211 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_208).2.2
                          )
                      )
                    change (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact (by
                      obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (4 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = ((4 : ℤ) : ℂ)))) h_208
                      have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) ∨ _enumerated_integer = (3 : ℤ) := by omega
                      rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value | _enumerated_value
                      · have _enumerated_case : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                        exact (by
                          have h_455 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_208
                                )
                            )
                          have h_456 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_455).1
                                )
                            )
                          have h_457 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_455).2.1
                                )
                            )
                          have h_458 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_455).2.2
                                )
                            )
                          have h_459 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  _enumerated_case
                                )
                            )
                          let _object_w9 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_456) (Litex.integerToComplex _value_i2 h_456))

                          have h_5 : (by
                            let _atomic_wd_1_0 := _object_w9
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := _object_w9
                                    exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_459 h_459)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
                                      let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                      exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (9 : ℂ)) (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                        have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                )
                            )
                          have h_4105 : (by
                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                )
                            )
                          have h_4184 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
                                    let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_4105)
                                )
                            )
                          show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                          exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_4105)
                        )
                      · have _enumerated_case : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                        exact (by
                          have h_4229 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_208
                                )
                            )
                          have h_4230 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_4229).1
                                )
                            )
                          have h_4231 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_4229).2.1
                                )
                            )
                          have h_4232 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_4229).2.2
                                )
                            )
                          have h_4233 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  _enumerated_case
                                )
                            )
                          let _object_w14 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_4230) (Litex.integerToComplex _value_i2 h_4230))

                          have h_5 : (by
                            let _atomic_wd_1_0 := _object_w14
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := _object_w14
                                    exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_4233 h_4233)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
                                      let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                      exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (9 : ℂ)) (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                        have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                )
                            )
                          have h_7876 : (by
                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                )
                            )
                          have h_7955 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
                                    let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_7876)
                                )
                            )
                          show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                          exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_7876)
                        )
                      · have _enumerated_case : Litex.denote _value_i2 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                        exact (by
                          have h_7996 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_208
                                )
                            )
                          have h_7997 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_7996).1
                                )
                            )
                          have h_7998 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_7996).2.1
                                )
                            )
                          have h_7999 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_7996).2.2
                                )
                            )
                          have h_8000 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  _enumerated_case
                                )
                            )
                          let _object_w19 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_7997) (Litex.integerToComplex _value_i2 h_7997))

                          have h_5 : (by
                            let _atomic_wd_1_0 := _object_w19
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := _object_w19
                                    exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_8000 h_8000)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
                                      let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                      exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (9 : ℂ)) (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                        have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                )
                            )
                          have h_11667 : (by
                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                )
                            )
                          have h_11746 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
                                    let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_11667)
                                )
                            )
                          show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                          exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_11667)
                        )
                      · have _enumerated_case : Litex.denote _value_i2 = M.number (3 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (3 : ℂ)))
                        exact (by
                          have h_11787 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_208
                                )
                            )
                          have h_11788 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_11787).1
                                )
                            )
                          have h_11789 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_11787).2.1
                                )
                            )
                          have h_11790 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_11787).2.2
                                )
                            )
                          have h_11791 : Litex.Same _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  _enumerated_case
                                )
                            )
                          let _object_w24 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_11788) (Litex.integerToComplex _value_i2 h_11788))

                          have h_5 : (by
                            let _atomic_wd_1_0 := _object_w24
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := _object_w24
                                    exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_11791 h_11791)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
                                      let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                                      exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (9 : ℂ)) (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                        have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                        let _atomic_wd_3_0 := _atomic_wd_2_0
                                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                          apply Complex.ofReal_injective
                                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                )
                            )
                          have h_15426 : (by
                            let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_0
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num)) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (9 : ℂ) (9 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                )
                            )
                          have h_15505 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
                                    let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
                                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                                        apply Complex.ofReal_injective
                                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                      let _atomic_wd_2_0 := _atomic_wd_1_1
                                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_15426)
                                )
                            )
                          show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                          exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_15426)
                        )
                    )
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_205) (Litex.integerToComplex _value_i1 h_205))
            exact (by
              have h_18365 : (by
                let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                exact Litex.In _value_i1 _atomic_wd_2_1) :=
                (by
                  let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                  exact h_204)
              exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) (congrArg₂ M.mulValue (Litex.sameRefl _value_i1) (Litex.sameRefl _value_i1)) (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_4 (Litex.denote _value)) _value_i1 h_18365))
            ))
        )
      )
  )

theorem h_18566 : (by
  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_18567 : (by
            let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
            exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                    exact (Litex.numberInRangeOfEq (M := M) (0 : ℂ) (4 : ℂ) (2 : ℂ) (0 : ℤ) (4 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
                )
            )
          have h_18571 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_18567).1
                )
            )
          have h_18572 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_18567).2.1
                )
            )
          have h_18573 : Litex.Lt (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_18567).2.2
                )
            )
          have h_18568 : Litex.Le (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (9 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18567)
                )
            )
          have h_18621 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
                    let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_18568)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
          exact h_18568)
        )
      )
  )

theorem h_18653 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (9 : ℂ) (9 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_18566 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit
