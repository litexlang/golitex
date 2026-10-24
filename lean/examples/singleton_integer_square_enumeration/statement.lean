import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_singleton_x5f_integer_x5f_square_x5f_enumeration_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := _wd_1_0;
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))))))), (by
  have h_11 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := _wd_1_0;
          (Litex.closedRange _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_10).1
        )
    )
  exact Litex.Same (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_11) (Litex.integerToComplex _value_i1 h_11)) (Litex.number (M := M) (4 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10
          have h_11 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := _wd_1_0;
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_10).1
                )
            )
          have h_12 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := _wd_1_0;
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_10).2.1
                )
            )
          have h_13 : Litex.Le _value_i1 (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := _wd_1_0;
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_10).2.2
                )
            )
          have h_14 : Litex.Same _value_i1 (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨k, hk, hlo, hhi⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := _wd_1_0;
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 (-2 : ℤ) (-2 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) h_10
                    have heq : k = (-2 : ℤ) := by omega
                    exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (- (2 : ℂ)))).trans ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).symm)
                  )
                )
            )
          change ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (4 : ℂ)))
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
            let _wd_1_1 := _wd_1_0;
            (Litex.closedRange _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 (-2 : ℤ) (-2 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) h_10
            have _enumerated_values : _enumerated_integer = (-2 : ℤ) := by omega
            have _enumerated_case : Litex.denote _value_i1 = M.number (-2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_values] : (_enumerated_integer : ℂ) = (-2 : ℂ)))
            exact (by
              have h_87 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
              let _wd_1_1 := _wd_1_0;
              (Litex.closedRange _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_10
                    )
                )
              have h_88 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                      let _wd_1_1 := _wd_1_0;
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_87).1
                    )
                )
              have h_89 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                      let _wd_1_1 := _wd_1_0;
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_87).2.1
                    )
                )
              have h_90 : Litex.Le _value_i1 (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                      let _wd_1_1 := _wd_1_0;
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 h_87).2.2
                    )
                )
              have h_91 : Litex.Same _value_i1 (Litex.number (M := M) (-2 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        obtain ⟨k, hk, hlo, hhi⟩ := Litex.inClosedRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                      let _wd_1_1 := _wd_1_0;
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))))) _value_i1 (-2 : ℤ) (-2 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) h_87
                        have heq : k = (-2 : ℤ) := by omega
                        exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (-2 : ℂ))).trans ((Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))).symm)
                      )
                    )
                )
              have h_92 : Litex.Same _value_i1 (Litex.number (M := M) (-2 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      _enumerated_case
                    )
                )
              let _object_w7 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_88) (Litex.integerToComplex _value_i1 h_88))

              have h_3 : (by
                let _equal_wd_1_0 := _object_w7
                exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (((congrArg₂ M.mulValue h_91 h_91)).trans (((let _equal_wd_2_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)));
                      (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) ((-2 : ℂ) * (-2 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))).symm))
                    )
                )
              have h_402 : (by
                let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)))
                exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (let _equal_wd_1_0 := (Litex.mul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)) (Litex.numberInC (M := M) (-2 : ℂ)));
                      (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) ((-2 : ℂ) * (-2 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (-2 : ℂ)) (Litex.number (M := M) (-2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num))))
                    )
                )
              show ((M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = (M.number (4 : ℂ)))
              exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => ((M.mulValue _enumeration_value _enumeration_value) = (M.number (4 : ℂ)))) _enumerated_case) (show ((M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) = (M.number (4 : ℂ))) from h_402)
            )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_singleton_x5f_integer_x5f_square_x5f_enumeration_x2f_statement_x2e_lit
