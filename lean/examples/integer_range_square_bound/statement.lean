import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_square_x5f_bound_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), (by
  have h_13 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_12).1
        )
    )
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_13) (Litex.integerToComplex _value_i1 h_13))
    exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12
          have h_13 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_12).1
                )
            )
          have h_14 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_12).2.1
                )
            )
          have h_15 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_12).2.2
                )
            )
          have h_16 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_12)
                )
            )
          have h_259 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_260 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_259).1
                )
            )
          have h_261 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_259).2.1
                )
            )
          have h_262 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_259).2.2
                )
            )
          have h_263 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_259)
                )
            )
          have h_271 : (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _expanded_range := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.inRangeInteger _expanded_range _value_i1 (1 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (by
                      let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                      exact h_259)
                    have _range_cases : _range_integer = (1 : ℤ) ∨ _range_integer = (2 : ℤ) := by omega
                    rcases _range_cases with _range_case | _range_case
                    · exact (Or.inl (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                    · exact (Or.inr (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                  )
                )
            )
          have _cases_result_512 : Litex.Le (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_260) (Litex.integerToComplex _value_i1 h_260)) (Litex.number (M := M) (4 : ℂ)) :=
            ((fun _litex_cases_tail => Or.elim _litex_cases_tail (fun (h_4 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) => by
            let _object_w12 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_260) (Litex.integerToComplex _value_i1 h_260))

            have h_5 : (by
              let _equal_wd_1_0 := _object_w12
              exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (((congrArg₂ M.mulValue h_4 h_4)).trans (((let _equal_wd_2_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) * (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))).symm))
                  )
              )
            have h_6 : (by
              let _atomic_wd_1_0 := _object_w12
              exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_1_0 := _object_w12
                      exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (h_5).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                  )
              )
            have h_3 : (by
              let _atomic_wd_1_0 := _object_w12
              exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_1_0 := _object_w12
                      exact h_6)
                  )
              )
            exact h_3
          ) (fun (h_7 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) => by
            let _object_w15 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_260) (Litex.integerToComplex _value_i1 h_260))

            have h_8 : (by
              let _equal_wd_1_0 := _object_w15
              exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (((congrArg₂ M.mulValue h_7 h_7)).trans (((let _equal_wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) ((2 : ℂ) * (2 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))).symm))
                  )
              )
            have h_9 : (by
              let _atomic_wd_1_0 := _object_w15
              exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_1_0 := _object_w15
                      exact (Litex.leOfSame (Litex.number (M := M) (4 : ℂ)) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (h_8).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                  )
              )
            have h_3 : (by
              let _atomic_wd_1_0 := _object_w15
              exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_1_0 := _object_w15
                      exact h_9)
                  )
              )
            exact h_3
          )) h_271)

          have h_3 : Litex.Le (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_260) (Litex.integerToComplex _value_i1 h_260)) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  _cases_result_512
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_260) (Litex.integerToComplex _value_i1 h_260))
            exact h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_square_x5f_bound_x2f_statement_x2e_lit
