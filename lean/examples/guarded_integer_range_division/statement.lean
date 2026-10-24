import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_integer_x5f_range_x5f_division_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.range _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  have h_10 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.range _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_9).1
        )
    )
  exact Litex.Same (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_10) (Litex.integerToComplex _value_i1 h_10) h_1) (Litex.number (M := M) (1 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 h_1
          have h_10 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_9).1
                )
            )
          have h_11 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_9).2.1
                )
            )
          have h_12 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_9).2.2
                )
            )
          change ((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ)))
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.range _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 (-1 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_9
            have _enumerated_values : _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case : Litex.denote _value_i1 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
              exact (by
                have h_88 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_9
                      )
                  )
                have h_89 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_88).1
                      )
                  )
                have h_90 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_88).2.1
                      )
                  )
                have h_91 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_88).2.2
                      )
                  )
                have h_92 : Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                have h_93 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) h_1)
                      )
                  )
                let _object_w11 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_89) (Litex.integerToComplex _value_i1 h_89) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_92).symm (show @Eq M.Value _ _ from Eq.refl _) h_93))

                have h_4 : (by
                  let _equal_wd_1_0 := _object_w11
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w11;
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_89)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_89))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_89)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_89))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_89)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_89)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_89)) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_92).symm (show @Eq M.Value _ _ from Eq.refl _) h_93)
                          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                        ))))
                      )
                  )
                have h_430 : (by
                  let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_93)
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_93);
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((-1 : ℂ) / (-1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                      )
                  )
                show ((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ)))
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ)))) _enumerated_case) (show ((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) from h_430)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                have h_459 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_9
                      )
                  )
                have h_460 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_459).1
                      )
                  )
                have h_461 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_459).2.1
                      )
                  )
                have h_462 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_459).2.2
                      )
                  )
                have h_463 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                have _excluded : ¬ ((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) := by
                  have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                  intro _source_guard
                  have _actual_guard := Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) _source_guard
                  exact _actual_guard _negative
                exact False.elim (_excluded h_1)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                have h_471 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_9
                      )
                  )
                have h_472 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_471).1
                      )
                  )
                have h_473 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_471).2.1
                      )
                  )
                have h_474 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_471).2.2
                      )
                  )
                have h_475 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                have h_476 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case) h_1)
                      )
                  )
                let _object_w25 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_472) (Litex.integerToComplex _value_i1 h_472) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_475).symm (show @Eq M.Value _ _ from Eq.refl _) h_476))

                have h_4 : (by
                  let _equal_wd_1_0 := _object_w25
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w25;
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_472)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_472))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_472)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_472))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_472)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_472)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_472)) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_475).symm (show @Eq M.Value _ _ from Eq.refl _) h_476)
                          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                        ))))
                      )
                  )
                have h_819 : (by
                  let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_476)
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_476);
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                      )
                  )
                show ((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ)))
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ)))) _enumerated_case) (show ((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) from h_819)
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_integer_x5f_range_x5f_division_x2f_statement_x2e_lit
