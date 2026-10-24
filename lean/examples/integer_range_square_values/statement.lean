import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_square_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))), (by
  have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_6).1
        )
    )
  exact Litex.Le (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i1 h_7)) (Litex.number (M := M) (9 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_6).1
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_6).2.1
                )
            )
          have h_9 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_6).2.2
                )
            )
          change (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 (0 : ℤ) (4 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = ((4 : ℤ) : ℂ)))) h_6
            have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) ∨ _enumerated_integer = (3 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                have h_202 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_203 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_202).1
                      )
                  )
                have h_204 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_202).2.1
                      )
                  )
                have h_205 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_202).2.2
                      )
                  )
                have h_206 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w9 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_203) (Litex.integerToComplex _value_i1 h_203))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w9
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w9
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_206 h_206)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
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
                have h_2969 : (by
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
                have h_3022 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_2969)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_2969)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                have h_3053 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_3054 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_3053).1
                      )
                  )
                have h_3055 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_3053).2.1
                      )
                  )
                have h_3056 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_3053).2.2
                      )
                  )
                have h_3057 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w18 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3054) (Litex.integerToComplex _value_i1 h_3054))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w18
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w18
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_3057 h_3057)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
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
                have h_5817 : (by
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
                have h_5870 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_5817)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_5817)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
              exact (by
                have h_5897 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_5898 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_5897).1
                      )
                  )
                have h_5899 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_5897).2.1
                      )
                  )
                have h_5900 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_5897).2.2
                      )
                  )
                have h_5901 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w27 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_5898) (Litex.integerToComplex _value_i1 h_5898))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w27
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w27
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_5901 h_5901)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
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
                have h_8689 : (by
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
                have h_8742 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_8689)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_8689)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (3 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (3 : ℂ)))
              exact (by
                have h_8769 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_6
                      )
                  )
                have h_8770 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8769).1
                      )
                  )
                have h_8771 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8769).2.1
                      )
                  )
                have h_8772 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i1 h_8769).2.2
                      )
                  )
                have h_8773 : Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w36 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_8770) (Litex.integerToComplex _value_i1 h_8770))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w36
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w36
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (9 : ℂ)) (Litex.number (M := M) (9 : ℂ)) ((congrArg₂ M.mulValue h_8773 h_8773)).symm (Litex.sameRefl (Litex.number (M := M) (9 : ℂ))) (by
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
                have h_11525 : (by
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
                have h_11578 : Litex.In (Litex.number (M := M) (9 : ℂ)) (Litex.N (M := M)) :=
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_11525)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (9 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_11525)
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_square_x5f_values_x2f_statement_x2e_lit
