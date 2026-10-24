import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_rectangle_x5f_square_x5f_bound_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_20 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (by
  have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).1
        )
    )
  have h_21 : Litex.In _value_i2 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_20).1
        )
    )
  exact Litex.Le (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i1 h_7));
  let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_21) (Litex.integerToComplex _value_i2 h_21));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_7) (Litex.integerToComplex _value_i1 h_7))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_21) (Litex.integerToComplex _value_i2 h_21))))) (Litex.number (M := M) (5 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_20
          have h_7 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).1
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).2.1
                )
            )
          have h_9 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_6).2.2
                )
            )
          have h_21 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_20).1
                )
            )
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_20).2.1
                )
            )
          have h_23 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_20).2.2
                )
            )
          change (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (0 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) h_6
            have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) ∨ _enumerated_integer = (2 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_20
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_1125 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_1126 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1125).1
                          )
                      )
                    have h_1127 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1125).2.1
                          )
                      )
                    have h_1128 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_1125).2.2
                          )
                      )
                    have h_1139 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_1140 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1139).1
                          )
                      )
                    have h_1141 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1139).2.1
                          )
                      )
                    have h_1142 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_1139).2.2
                          )
                      )
                    have h_1143 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_1144 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w13 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1126) (Litex.integerToComplex _value_i1 h_1126));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_1143).trans (h_1144).symm) (show @Eq M.Value _ _ from Eq.refl _) h_1126)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_1143).trans (h_1144).symm) (show @Eq M.Value _ _ from Eq.refl _) h_1126)));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1126) (Litex.integerToComplex _value_i1 h_1126))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_1143).trans (h_1144).symm) (show @Eq M.Value _ _ from Eq.refl _) h_1126)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_1143).trans (h_1144).symm) (show @Eq M.Value _ _ from Eq.refl _) h_1126))))))

                    have h_3 : (by
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
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_1143 h_1143) (congrArg₂ M.mulValue h_1144 h_1144))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_26665 : (by
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
                    have h_26998 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_26665)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_26665)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_27049 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_27050 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_27049).1
                          )
                      )
                    have h_27051 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_27049).2.1
                          )
                      )
                    have h_27052 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_27049).2.2
                          )
                      )
                    have h_27063 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_27064 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27063).1
                          )
                      )
                    have h_27065 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27063).2.1
                          )
                      )
                    have h_27066 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_27063).2.2
                          )
                      )
                    have h_27067 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_27068 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w24 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_27050) (Litex.integerToComplex _value_i1 h_27050));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_27064) (Litex.integerToComplex _value_i2 h_27064));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_27050) (Litex.integerToComplex _value_i1 h_27050))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_27064) (Litex.integerToComplex _value_i2 h_27064)))))

                    have h_3 : (by
                      let _atomic_wd_1_0 := _object_w24
                      exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w24
                              exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                              let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_27067 h_27067) (congrArg₂ M.mulValue h_27068 h_27068))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_48524 : (by
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
                    have h_48793 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_48524)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_48524)
                  )
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_20
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_48840 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_48841 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_48840).1
                          )
                      )
                    have h_48842 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_48840).2.1
                          )
                      )
                    have h_48843 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_48840).2.2
                          )
                      )
                    have h_48854 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_48855 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_48854).1
                          )
                      )
                    have h_48856 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_48854).2.1
                          )
                      )
                    have h_48857 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_48854).2.2
                          )
                      )
                    have h_48858 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_48859 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w35 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_48841) (Litex.integerToComplex _value_i1 h_48841));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_48855) (Litex.integerToComplex _value_i2 h_48855));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_48841) (Litex.integerToComplex _value_i1 h_48841))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_48855) (Litex.integerToComplex _value_i2 h_48855)))))

                    have h_3 : (by
                      let _atomic_wd_1_0 := _object_w35
                      exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w35
                              exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                              let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_48858 h_48858) (congrArg₂ M.mulValue h_48859 h_48859))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_70315 : (by
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
                    have h_70584 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_70315)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_70315)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_70631 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_70632 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_70631).1
                          )
                      )
                    have h_70633 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_70631).2.1
                          )
                      )
                    have h_70634 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_70631).2.2
                          )
                      )
                    have h_70645 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_70646 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_70645).1
                          )
                      )
                    have h_70647 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_70645).2.1
                          )
                      )
                    have h_70648 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_70645).2.2
                          )
                      )
                    have h_70649 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_70650 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w46 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_70632) (Litex.integerToComplex _value_i1 h_70632));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_70649).trans (h_70650).symm) (show @Eq M.Value _ _ from Eq.refl _) h_70632)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_70649).trans (h_70650).symm) (show @Eq M.Value _ _ from Eq.refl _) h_70632)));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_70632) (Litex.integerToComplex _value_i1 h_70632))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_70649).trans (h_70650).symm) (show @Eq M.Value _ _ from Eq.refl _) h_70632)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_70649).trans (h_70650).symm) (show @Eq M.Value _ _ from Eq.refl _) h_70632))))))

                    have h_3 : (by
                      let _atomic_wd_1_0 := _object_w46
                      exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w46
                              exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                              let _wd_1_1 := _wd_1_0;
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_70649 h_70649) (congrArg₂ M.mulValue h_70650 h_70650))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_96185 : (by
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
                    have h_96518 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_96185)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_96185)
                  )
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (0 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_20
                have _enumerated_values : _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_96561 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_96562 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_96561).1
                          )
                      )
                    have h_96563 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_96561).2.1
                          )
                      )
                    have h_96564 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_96561).2.2
                          )
                      )
                    have h_96575 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_96576 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_96575).1
                          )
                      )
                    have h_96577 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_96575).2.1
                          )
                      )
                    have h_96578 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_96575).2.2
                          )
                      )
                    have h_96579 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_96580 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w56 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_96562) (Litex.integerToComplex _value_i1 h_96562));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_96576) (Litex.integerToComplex _value_i2 h_96576));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_96562) (Litex.integerToComplex _value_i1 h_96562))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_96576) (Litex.integerToComplex _value_i2 h_96576)))))

                    have h_3 : (by
                      let _atomic_wd_1_0 := _object_w56
                      exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w56
                              exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                              let _wd_1_1 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) * (0 : ℂ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_96579 h_96579) (congrArg₂ M.mulValue h_96580 h_96580))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_118108 : (by
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
                    have h_118377 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_118108)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_118108)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_118424 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6
                          )
                      )
                    have h_118425 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_118424).1
                          )
                      )
                    have h_118426 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_118424).2.1
                          )
                      )
                    have h_118427 : Litex.Lt _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_118424).2.2
                          )
                      )
                    have h_118438 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    have h_118439 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_118438).1
                          )
                      )
                    have h_118440 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_118438).2.1
                          )
                      )
                    have h_118441 : Litex.Lt _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_118438).2.2
                          )
                      )
                    have h_118442 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_118443 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    let _object_w67 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_118425) (Litex.integerToComplex _value_i1 h_118425));
                    let _wd_1_1 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_118439) (Litex.integerToComplex _value_i2 h_118439));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_118425) (Litex.integerToComplex _value_i1 h_118425))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_118439) (Litex.integerToComplex _value_i2 h_118439)))))

                    have h_3 : (by
                      let _atomic_wd_1_0 := _object_w67
                      exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w67
                              exact (Litex.leOfSame (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                              let _wd_1_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                              (Litex.add _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) * (2 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (by
                                let _atomic_wd_2_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) * (1 : ℂ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) _atomic_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((congrArg₂ M.addValue (congrArg₂ M.mulValue h_118442 h_118442) (congrArg₂ M.mulValue h_118443 h_118443))).symm (Litex.sameRefl (Litex.number (M := M) (5 : ℂ))) (by
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
                    have h_139978 : (by
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
                    have h_140247 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.N (M := M)) :=
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
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_139978)
                          )
                      )
                    show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue _enumeration_value _enumeration_value) (M.mulValue (Litex.denote _value_i2) (Litex.denote _value_i2))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue _enumeration_value _enumeration_value)) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case_1)) (show (∃ (_r _s : ℝ), (M.addValue (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_139978)
                  )
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_rectangle_x5f_square_x5f_bound_x2f_statement_x2e_lit
