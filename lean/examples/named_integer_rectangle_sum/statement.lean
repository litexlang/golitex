import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_rectangle_x5f_sum_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), (by
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
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_22).1
        )
    )
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_9) (Litex.integerToComplex _value_i2 h_23))
    exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)))
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
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_22).1
                )
            )
          have h_24 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_22).2.1
                )
            )
          have h_25 : Litex.Lt _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_22).2.2
                )
            )
          have h_26 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_22)
                )
            )
          have h_310 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_324 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_311 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_310).1
                )
            )
          have h_312 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_310).2.1
                )
            )
          have h_313 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_310).2.2
                )
            )
          have h_325 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_324).1
                )
            )
          have h_326 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_324).2.1
                )
            )
          have h_327 : Litex.Lt _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_324).2.2
                )
            )
          have h_328 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_324)
                )
            )
          have h_4 : ∀ (_enumerated_i3 : M.Value) (h_329 : M.mem _enumerated_i3 (Litex.denote (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))) (_enumerated_i4 : M.Value) (h_333 : M.mem _enumerated_i4 (Litex.denote (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))), (∃ (_r _s : ℝ), (M.addValue _enumerated_i3 _enumerated_i4) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _enumerated_i3 h_329 _enumerated_i4 h_333
                    let _value_i3 := Litex.semanticObject _enumerated_i3 (M.member_isSet h_329)
                    let _value_i4 := Litex.semanticObject _enumerated_i4 (M.member_isSet h_333)
                    have h_330 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_329).1
                          )
                      )
                    have h_331 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_329).2.1
                          )
                      )
                    have h_332 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_329).2.2
                          )
                      )
                    have h_334 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_333).1
                          )
                      )
                    have h_335 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_333).2.1
                          )
                      )
                    have h_336 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_333).2.2
                          )
                      )
                    have h_337 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_333)
                          )
                      )
                    change (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact (by
                      obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 (0 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_329
                      have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
                      rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_333
                          have _enumerated_values : _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_751 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_752 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_751).1
                                    )
                                )
                              have h_753 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_751).2.1
                                    )
                                )
                              have h_754 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_751).2.2
                                    )
                                )
                              have h_755 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_756 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_755).1
                                    )
                                )
                              have h_757 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_755).2.1
                                    )
                                )
                              have h_758 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_755).2.2
                                    )
                                )
                              have h_759 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_755)
                                    )
                                )
                              have h_760 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_761 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w15 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_752) (Litex.integerToComplex _value_i4 h_756))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w15
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w15
                                        exact (Litex.addLeOfLeOfNonposSwap _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.leTrans _value_i4 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.ltToLe _value_i4 (Litex.number (M := M) (3 : ℂ)) h_758) (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℝ) (4 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num))) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) _value_i3 _value_i3 (Litex.number (M := M) (0 : ℂ)) (h_760).symm h_760 h_753)))
                                    )
                                )
                              have h_10828 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_10985 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_10828)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (0 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_10828)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                            exact (by
                              have h_11070 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_11071 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_11070).1
                                    )
                                )
                              have h_11072 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_11070).2.1
                                    )
                                )
                              have h_11073 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_11070).2.2
                                    )
                                )
                              have h_11074 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_11075 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_11074).1
                                    )
                                )
                              have h_11076 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_11074).2.1
                                    )
                                )
                              have h_11077 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_11074).2.2
                                    )
                                )
                              have h_11078 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_11074)
                                    )
                                )
                              have h_11079 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_11080 : Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w20 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_11071) (Litex.integerToComplex _value_i4 h_11075))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w20
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w20
                                        exact (Litex.addLeOfLeOfNonposSwap _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.leTrans _value_i4 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.ltToLe _value_i4 (Litex.number (M := M) (3 : ℂ)) h_11077) (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (3 : ℝ) (4 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num))) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) _value_i3 _value_i3 (Litex.number (M := M) (0 : ℂ)) (h_11079).symm h_11079 h_11072)))
                                    )
                                )
                              have h_21267 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_21424 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) + (2 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_21267)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (0 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (0 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_21267)
                            )
                        )
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_333
                          have _enumerated_values : _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_21509 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_21510 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_21509).1
                                    )
                                )
                              have h_21511 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_21509).2.1
                                    )
                                )
                              have h_21512 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_21509).2.2
                                    )
                                )
                              have h_21513 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_21514 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_21513).1
                                    )
                                )
                              have h_21515 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_21513).2.1
                                    )
                                )
                              have h_21516 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_21513).2.2
                                    )
                                )
                              have h_21517 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_21513)
                                    )
                                )
                              have h_21518 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_21519 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w24 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_21510) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_21518).trans (h_21519).symm) (show @Eq M.Value _ _ from Eq.refl _) h_21510)))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w24
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w24
                                        exact (Litex.leOfSame (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.addValue h_21518 h_21519)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                                          let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_34698 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_34875 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_34698)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (1 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_34698)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                            exact (by
                              have h_34956 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_34957 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_34956).1
                                    )
                                )
                              have h_34958 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_34956).2.1
                                    )
                                )
                              have h_34959 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_34956).2.2
                                    )
                                )
                              have h_34960 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_34961 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_34960).1
                                    )
                                )
                              have h_34962 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_34960).2.1
                                    )
                                )
                              have h_34963 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_34960).2.2
                                    )
                                )
                              have h_34964 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_34960)
                                    )
                                )
                              have h_34965 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_34966 : Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w29 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_34957) (Litex.integerToComplex _value_i4 h_34961))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w29
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w29
                                        exact (Litex.leOfSame (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.addValue h_34965 h_34966)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                                          let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_47103 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_47260 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (2 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_47103)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (1 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_47103)
                            )
                        )
                      · have _enumerated_case_0 : Litex.denote _value_i3 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                        exact (by
                          obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_333
                          have _enumerated_values : _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
                          rcases _enumerated_values with _enumerated_value | _enumerated_value
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                            exact (by
                              have h_47341 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_47342 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_47341).1
                                    )
                                )
                              have h_47343 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_47341).2.1
                                    )
                                )
                              have h_47344 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_47341).2.2
                                    )
                                )
                              have h_47345 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_47346 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_47345).1
                                    )
                                )
                              have h_47347 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_47345).2.1
                                    )
                                )
                              have h_47348 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_47345).2.2
                                    )
                                )
                              have h_47349 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_47345)
                                    )
                                )
                              have h_47350 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_47351 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w34 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_47342) (Litex.integerToComplex _value_i4 h_47346))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w34
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w34
                                        exact (Litex.leOfSame (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.addValue h_47350 h_47351)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                                          let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_59400 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_59557 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_59400)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (2 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_59400)
                            )
                          · have _enumerated_case_1 : Litex.denote _value_i4 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
                            exact (by
                              have h_59638 : Litex.In _value_i3 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_329
                                    )
                                )
                              have h_59639 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_59638).1
                                    )
                                )
                              have h_59640 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_59638).2.1
                                    )
                                )
                              have h_59641 : Litex.Lt _value_i3 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i3 h_59638).2.2
                                    )
                                )
                              have h_59642 : Litex.In _value_i4 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_333
                                    )
                                )
                              have h_59643 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_59642).1
                                    )
                                )
                              have h_59644 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_59642).2.1
                                    )
                                )
                              have h_59645 : Litex.Lt _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_59642).2.2
                                    )
                                )
                              have h_59646 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_59642)
                                    )
                                )
                              have h_59647 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_0
                                    )
                                )
                              have h_59648 : Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      _enumerated_case_1
                                    )
                                )
                              let _object_w39 := (Litex.add _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_59639) (Litex.integerToComplex _value_i4 (Litex.inOfSame _value_i3 _value_i4 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_59647).trans (h_59648).symm) (show @Eq M.Value _ _ from Eq.refl _) h_59639)))

                              have h_5 : (by
                                let _atomic_wd_1_0 := _object_w39
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w39
                                        exact (Litex.leOfSame (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.addValue h_59647 h_59648)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                                          let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                                            let _atomic_wd_3_0 := _atomic_wd_2_0
                                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                              apply Complex.ofReal_injective
                                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                                    )
                                )
                              have h_73075 : (by
                                let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                                    )
                                )
                              have h_73252 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                                        let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                                        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
                                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                            apply Complex.ofReal_injective
                                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                                          let _atomic_wd_2_0 := _atomic_wd_1_1
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_73075)
                                    )
                                )
                              show (∃ (_r _s : ℝ), (M.addValue (Litex.denote _value_i3) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                              exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue _enumeration_value (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.number (2 : ℂ)) _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_73075)
                            )
                        )
                    )
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.add _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_311) (Litex.integerToComplex _value_i2 h_325))
            exact (by
              have h_81003 : (by
                let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                exact Litex.In _value_i1 _atomic_wd_2_1) :=
                (by
                  let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                  exact h_310)
              have h_81008 : (by
                let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                exact Litex.In _value_i2 _atomic_wd_2_1) :=
                (by
                  let _atomic_wd_2_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                  exact h_324)
              exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (congrArg₂ M.addValue (Litex.sameRefl _value_i1) (Litex.sameRefl _value_i2)) (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) ((fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) h_329 {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) h_333 => h_4 (Litex.denote _value_i3) h_329 (Litex.denote _value_i4) h_333) _value_i1 h_81003 _value_i2 h_81008))
            ))
        )
      )
  )

theorem h_81319 : (by
  let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_81320 : (by
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
          have h_81325 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81320).1
                )
            )
          have h_81326 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81320).2.1
                )
            )
          have h_81327 : Litex.Lt (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81320).2.2
                )
            )
          have h_81321 : (by
            let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    exact (Litex.numberInRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
                )
            )
          have h_81346 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81321).1
                )
            )
          have h_81347 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81321).2.1
                )
            )
          have h_81348 : Litex.Lt (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) h_81321).2.2
                )
            )
          have h_81349 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.number (M := M) (2 : ℂ)) (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_81321)
                )
            )
          have h_81322 : Litex.Le (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_81320 (Litex.number (M := M) (2 : ℂ)) h_81321)
                )
            )
          have h_81458 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                    let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_81322)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
          exact h_81322)
        )
      )
  )

theorem h_81511 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) + (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_81319 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_integer_x5f_rectangle_x5f_sum_x2f_statement_x2e_lit
