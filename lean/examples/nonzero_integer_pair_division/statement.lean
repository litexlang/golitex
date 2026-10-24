import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_integer_x5f_pair_x5f_division_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  have h_13 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.closedRange _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_12).1
        )
    )
  have h_17 : Litex.In _value_i2 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.closedRange _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_16).1
        )
    )
  exact (Litex.Same (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_13) (Litex.integerToComplex _value_i1 h_13) h_1) (Litex.number (M := M) (1 : ℂ)) ∧ Litex.Same (Litex.div _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_17) (Litex.integerToComplex _value_i2 h_17) h_2) (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12 _Host_i2 _rep_i2 _value_i2 h_16 h_1 h_2
          have h_13 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_12).1
                )
            )
          have h_14 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_12).2.1
                )
            )
          have h_15 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_12).2.2
                )
            )
          have h_17 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_16).1
                )
            )
          have h_18 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_16).2.1
                )
            )
          have h_19 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_16).2.2
                )
            )
          change (((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.closedRange _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 (-1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_12
            have _enumerated_values : _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 (-1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_16
                have _enumerated_values : _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
                  exact (by
                    have h_201 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_202 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_201).1
                          )
                      )
                    have h_203 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_201).2.1
                          )
                      )
                    have h_204 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_201).2.2
                          )
                      )
                    have h_205 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_206 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_205).1
                          )
                      )
                    have h_207 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_205).2.1
                          )
                      )
                    have h_208 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_205).2.2
                          )
                      )
                    have h_209 : Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_210 : Litex.Same _value_i2 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_211 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have h_273 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) h_2)
                          )
                      )
                    let _object_w11 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_202) (Litex.integerToComplex _value_i1 h_202) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_209).symm (show @Eq M.Value _ _ from Eq.refl _) h_211))

                    have h_6 : (by
                      let _equal_wd_1_0 := _object_w11
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w11;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_202)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_202))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_202)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_202))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_202)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_202)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_202)) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_209).symm (show @Eq M.Value _ _ from Eq.refl _) h_211)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    let _object_w12 := (Litex.div _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202)) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_210).symm (show @Eq M.Value _ _ from Eq.refl _) h_211))

                    have h_7 : (by
                      let _equal_wd_1_0 := _object_w12
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w12;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202))) / (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_209).trans (h_210).symm) (show @Eq M.Value _ _ from Eq.refl _) h_202))) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_210).symm (show @Eq M.Value _ _ from Eq.refl _) h_211)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    have h_1261 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_211)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_211);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((-1 : ℂ) / (-1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    have h_1302 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_211)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1261
                          )
                      )
                    show (((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) ∧ ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))))) _enumerated_case_1)) (And.intro (show ((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) from h_1261) (show ((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) from h_1302))
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_1308 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_1309 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1308).1
                          )
                      )
                    have h_1310 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1308).2.1
                          )
                      )
                    have h_1311 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1308).2.2
                          )
                      )
                    have h_1312 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_1313 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1312).1
                          )
                      )
                    have h_1314 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1312).2.1
                          )
                      )
                    have h_1315 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1312).2.2
                          )
                      )
                    have h_1316 : Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_1317 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_1318 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have _excluded : ¬ ((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) := by
                      have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                      intro _source_guard
                      have _actual_guard := Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) _source_guard
                      exact _actual_guard _negative
                    exact False.elim (_excluded h_2)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_1423 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_1424 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1423).1
                          )
                      )
                    have h_1425 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1423).2.1
                          )
                      )
                    have h_1426 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_1423).2.2
                          )
                      )
                    have h_1427 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_1428 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1427).1
                          )
                      )
                    have h_1429 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1427).2.1
                          )
                      )
                    have h_1430 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_1427).2.2
                          )
                      )
                    have h_1431 : Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_1432 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_1433 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have h_1473 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) h_2)
                          )
                      )
                    let _object_w24 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1424) (Litex.integerToComplex _value_i1 h_1424) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_1431).symm (show @Eq M.Value _ _ from Eq.refl _) h_1433))

                    have h_6 : (by
                      let _equal_wd_1_0 := _object_w24
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w24;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1424)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1424))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_1424)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_1424))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1424)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_1424)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_1424)) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_1431).symm (show @Eq M.Value _ _ from Eq.refl _) h_1433)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    let _object_w25 := (Litex.div _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_1428) (Litex.integerToComplex _value_i2 h_1428) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_1432).symm (show @Eq M.Value _ _ from Eq.refl _) h_1473))

                    have h_7 : (by
                      let _equal_wd_1_0 := _object_w25
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w25;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_1428)) / (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_1428))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_1428)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_1428))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_1428)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_1428)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_1428)) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_1432).symm (show @Eq M.Value _ _ from Eq.refl _) h_1473)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    have h_2298 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_1433)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_1433);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((-1 : ℂ) / (-1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    have h_2331 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_1473)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_1473);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    show (((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) ∧ ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))))) _enumerated_case_1)) (And.intro (show ((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) from h_2298) (show ((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) from h_2331))
                  )
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 (-1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_16
                have _enumerated_values : _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
                  exact (by
                    have h_2370 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_2371 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2370).1
                          )
                      )
                    have h_2372 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2370).2.1
                          )
                      )
                    have h_2373 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2370).2.2
                          )
                      )
                    have h_2374 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_2375 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2374).1
                          )
                      )
                    have h_2376 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2374).2.1
                          )
                      )
                    have h_2377 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2374).2.2
                          )
                      )
                    have h_2378 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_2379 : Litex.Same _value_i2 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have _excluded : ¬ ((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) := by
                      have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                      intro _source_guard
                      have _actual_guard := Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (0 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) _source_guard
                      exact _actual_guard _negative
                    exact False.elim (_excluded h_1)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_2387 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_2388 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2387).1
                          )
                      )
                    have h_2389 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2387).2.1
                          )
                      )
                    have h_2390 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2387).2.2
                          )
                      )
                    have h_2391 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_2392 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2391).1
                          )
                      )
                    have h_2393 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2391).2.1
                          )
                      )
                    have h_2394 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2391).2.2
                          )
                      )
                    have h_2395 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_2396 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have _excluded : ¬ ((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) := by
                      have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                      intro _source_guard
                      have _actual_guard := Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (0 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) _source_guard
                      exact _actual_guard _negative
                    exact False.elim (_excluded h_1)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_2404 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_2405 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2404).1
                          )
                      )
                    have h_2406 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2404).2.1
                          )
                      )
                    have h_2407 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2404).2.2
                          )
                      )
                    have h_2408 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_2409 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2408).1
                          )
                      )
                    have h_2410 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2408).2.1
                          )
                      )
                    have h_2411 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2408).2.2
                          )
                      )
                    have h_2412 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_2413 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have _excluded : ¬ ((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) := by
                      have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                      intro _source_guard
                      have _actual_guard := Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (0 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) _source_guard
                      exact _actual_guard _negative
                    exact False.elim (_excluded h_1)
                  )
              )
            · have _enumerated_case_0 : Litex.denote _value_i1 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
              exact (by
                obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                (Litex.closedRange _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 (-1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_16
                have _enumerated_values : _enumerated_integer = (-1 : ℤ) ∨ _enumerated_integer = (0 : ℤ) ∨ _enumerated_integer = (1 : ℤ) := by omega
                rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (-1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (-1 : ℂ)))
                  exact (by
                    have h_2421 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_2422 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2421).1
                          )
                      )
                    have h_2423 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2421).2.1
                          )
                      )
                    have h_2424 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_2421).2.2
                          )
                      )
                    have h_2425 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_2426 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2425).1
                          )
                      )
                    have h_2427 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2425).2.1
                          )
                      )
                    have h_2428 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_2425).2.2
                          )
                      )
                    have h_2429 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_2430 : Litex.Same _value_i2 (Litex.number (M := M) (-1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_2431 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have h_2467 : ¬ Litex.Same (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (-1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) h_2)
                          )
                      )
                    let _object_w48 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_2422) (Litex.integerToComplex _value_i1 h_2422) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_2429).symm (show @Eq M.Value _ _ from Eq.refl _) h_2431))

                    have h_6 : (by
                      let _equal_wd_1_0 := _object_w48
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w48;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_2422)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_2422))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_2422)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_2422))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_2422)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_2422)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_2422)) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_2429).symm (show @Eq M.Value _ _ from Eq.refl _) h_2431)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    let _object_w49 := (Litex.div _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_2426) (Litex.integerToComplex _value_i2 h_2426) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_2430).symm (show @Eq M.Value _ _ from Eq.refl _) h_2467))

                    have h_7 : (by
                      let _equal_wd_1_0 := _object_w49
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w49;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_2426)) / (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_2426))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_2426)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_2426))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_2426)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 h_2426)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 h_2426)) (Litex.notSameOfSame (Litex.number (M := M) (-1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_2430).symm (show @Eq M.Value _ _ from Eq.refl _) h_2467)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    have h_3296 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_2431)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_2431);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    have h_3329 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_2467)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) (Litex.numberInC (M := M) (-1 : ℂ)) h_2467);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((-1 : ℂ) / (-1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (-1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    show (((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) ∧ ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))))) _enumerated_case_1)) (And.intro (show ((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) from h_3296) (show ((M.divValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = (M.number (1 : ℂ))) from h_3329))
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (0 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (0 : ℂ)))
                  exact (by
                    have h_3368 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_3369 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3368).1
                          )
                      )
                    have h_3370 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3368).2.1
                          )
                      )
                    have h_3371 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3368).2.2
                          )
                      )
                    have h_3372 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_3373 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3372).1
                          )
                      )
                    have h_3374 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3372).2.1
                          )
                      )
                    have h_3375 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3372).2.2
                          )
                      )
                    have h_3376 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_3377 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_3378 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have _excluded : ¬ ((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) := by
                      have _negative : ((M.number (0 : ℂ)) = (M.number (0 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                      intro _source_guard
                      have _actual_guard := Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) _source_guard
                      exact _actual_guard _negative
                    exact False.elim (_excluded h_2)
                  )
                · have _enumerated_case_1 : Litex.denote _value_i2 = M.number (1 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (1 : ℂ)))
                  exact (by
                    have h_3454 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_12
                          )
                      )
                    have h_3455 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3454).1
                          )
                      )
                    have h_3456 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3454).2.1
                          )
                      )
                    have h_3457 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_3454).2.2
                          )
                      )
                    have h_3458 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_16
                          )
                      )
                    have h_3459 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3458).1
                          )
                      )
                    have h_3460 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3458).2.1
                          )
                      )
                    have h_3461 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                            (Litex.closedRange _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := _wd_1_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i2 h_3458).2.2
                          )
                      )
                    have h_3462 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_0
                          )
                      )
                    have h_3463 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            _enumerated_case_1
                          )
                      )
                    have h_3464 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ))))) _enumerated_case_1)) h_1)
                          )
                      )
                    have h_3520 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (¬ ((M.number (1 : ℂ)) = (M.number (0 : ℂ)))) from Eq.mp (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (0 : ℂ))))) _enumerated_case_1)) h_2)
                          )
                      )
                    let _object_w62 := (Litex.div _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3455) (Litex.integerToComplex _value_i1 h_3455) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_3462).symm (show @Eq M.Value _ _ from Eq.refl _) h_3464))

                    have h_6 : (by
                      let _equal_wd_1_0 := _object_w62
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w62;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3455)) / (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3455))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_3455)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_3455))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3455)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.integerToComplex _value_i1 h_3455)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.integerToComplex _value_i1 h_3455)) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_3462).symm (show @Eq M.Value _ _ from Eq.refl _) h_3464)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    let _object_w63 := (Litex.div _value_i2 _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455)) (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455)) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_3463).symm (show @Eq M.Value _ _ from Eq.refl _) h_3464))

                    have h_7 : (by
                      let _equal_wd_1_0 := _object_w63
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w63;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455))) / (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.integerToComplex _value_i2 (Litex.inOfSame _value_i1 _value_i2 (Litex.Z (M := M)) (Litex.Z (M := M)) ((h_3462).trans (h_3463).symm) (show @Eq M.Value _ _ from Eq.refl _) h_3455))) (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_3463).symm (show @Eq M.Value _ _ from Eq.refl _) h_3464)
                              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                            ))))
                          )
                      )
                    have h_4534 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_3464)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_3464);
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                          )
                      )
                    have h_4575 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) h_3464)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4534
                          )
                      )
                    show (((M.divValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))
                    exact Eq.mpr (Eq.trans (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))) ∧ ((M.divValue (Litex.denote _value_i2) (Litex.denote _value_i2)) = (M.number (1 : ℂ))))) _enumerated_case_0) (congrArg (fun (_enumeration_value : M.Value) => (((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) ∧ ((M.divValue _enumeration_value _enumeration_value) = (M.number (1 : ℂ))))) _enumerated_case_1)) (And.intro (show ((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) from h_4534) (show ((M.divValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.number (1 : ℂ))) from h_4575))
                  )
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_integer_x5f_pair_x5f_division_x2f_statement_x2e_lit
