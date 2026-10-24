import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_integer_x5f_square_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))), (by
  have h_9 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.closedRange _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8).1
        )
    )
  exact Litex.Le (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_9) (Litex.integerToComplex _value_i1 h_9)) (Litex.number (M := M) (4 : ℂ))
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
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8).1
                )
            )
          have h_10 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8).2.1
                )
            )
          have h_11 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8).2.2
                )
            )
          change (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.closedRange _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 (-2 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_8
            have _enumerated_values : _enumerated_integer = (-2 : ℤ) ∨ _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case : Litex.denote _value_i1 = M.number (-2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-2 : ℂ)))
              exact (by
                have h_207 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_8
                      )
                  )
                have h_208 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_207).1
                      )
                  )
                have h_209 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_207).2.1
                      )
                  )
                have h_210 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_207).2.2
                      )
                  )
                have h_211 : Litex.Same _value_i1 (Litex.number (M := M) (-2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w9 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_208) (Litex.integerToComplex _value_i1 h_208))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w9
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w9
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.mulValue h_211 h_211)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_2970 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_3025 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                          let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num))))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-2 : ℂ) * (-2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-2 : ℂ) * (-2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_2970)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_2970)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
              exact (by
                have h_3054 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_8
                      )
                  )
                have h_3055 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3054).1
                      )
                  )
                have h_3056 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3054).2.1
                      )
                  )
                have h_3057 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3054).2.2
                      )
                  )
                have h_3058 : Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w18 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3055) (Litex.integerToComplex _value_i1 h_3055))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w18
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w18
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.mulValue h_3058 h_3058)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_5817 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_5872 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
                          let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num))))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((-1 : ℂ) * (-1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-1 : ℂ) * (-1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_5817)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_5817)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                have h_5901 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_8
                      )
                  )
                have h_5902 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_5901).1
                      )
                  )
                have h_5903 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_5901).2.1
                      )
                  )
                have h_5904 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_5901).2.2
                      )
                  )
                have h_5905 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w27 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_5902) (Litex.integerToComplex _value_i1 h_5902))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w27
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w27
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.mulValue h_5905 h_5905)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_8677 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num)))) = (0 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((0 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_8732 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_8677)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_8677)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                have h_8767 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_8
                      )
                  )
                have h_8768 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8767).1
                      )
                  )
                have h_8769 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8767).2.1
                      )
                  )
                have h_8770 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                        (Litex.closedRange _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_8767).2.2
                      )
                  )
                have h_8771 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w35 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_8768) (Litex.integerToComplex _value_i1 h_8768))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w35
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w35
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((congrArg₂ M.mulValue h_8771 h_8771)).symm (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_11538 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (4 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num)))) = (1 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) * (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) * (1 : ℂ)) (1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_11593 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (by
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_11538)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (4 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_11538)
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_integer_x5f_square_x5f_values_x2f_statement_x2e_lit
