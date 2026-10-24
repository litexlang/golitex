import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_calculated_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_14 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.range _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num))))))), (by
  have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.range _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_14).1
        )
    )
  exact Litex.Le (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_15) (Litex.integerToComplex _value_i1 h_15)) (Litex.number (M := M) (16 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_14
          have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_14).1
                )
            )
          have h_16 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_14).2.1
                )
            )
          have h_17 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_14).2.2
                )
            )
          change (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
          exact (by
            obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.inRangeInteger (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
            let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
            (Litex.range _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 (2 : ℤ) (5 : ℤ) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) + (2 : ℂ)) = ((5 : ℤ) : ℂ)))) h_14
            have _enumerated_values : _enumerated_integer = (2 : ℤ) ∨ _enumerated_integer = (3 : ℤ) ∨ _enumerated_integer = (4 : ℤ) := by omega
            rcases _enumerated_values with _enumerated_value | _enumerated_value | _enumerated_value
            · have _enumerated_case : Litex.denote _value_i1 = M.number (2 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (2 : ℂ)))
              exact (by
                have h_218 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_14
                      )
                  )
                have h_219 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_218).1
                      )
                  )
                have h_220 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_218).2.1
                      )
                  )
                have h_221 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_218).2.2
                      )
                  )
                have h_222 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w10 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_219) (Litex.integerToComplex _value_i1 h_219))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w10
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w10
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (Litex.number (M := M) (16 : ℂ)) ((congrArg₂ M.mulValue h_222 h_222)).symm (Litex.sameRefl (Litex.number (M := M) (16 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (16 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_3005 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num)))) = (4 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) * (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) * (2 : ℂ)) (4 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_3058 : Litex.In (Litex.number (M := M) (16 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (16 : ℂ) (16 : ℤ) (by norm_num)) (by
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_3005)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_3005)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (3 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (3 : ℂ)))
              exact (by
                have h_3091 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_14
                      )
                  )
                have h_3092 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_3091).1
                      )
                  )
                have h_3093 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_3091).2.1
                      )
                  )
                have h_3094 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_3091).2.2
                      )
                  )
                have h_3095 : Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w19 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3092) (Litex.integerToComplex _value_i1 h_3092))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w19
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w19
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (Litex.number (M := M) (16 : ℂ)) ((congrArg₂ M.mulValue h_3095 h_3095)).symm (Litex.sameRefl (Litex.number (M := M) (16 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (16 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_5842 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_5895 : Litex.In (Litex.number (M := M) (16 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (16 : ℂ) (16 : ℤ) (by norm_num)) (by
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
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_5842)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_5842)
              )
            · have _enumerated_case : Litex.denote _value_i1 = M.number (4 : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [_enumerated_value] : (_enumerated_integer : ℂ) = (4 : ℂ)))
              exact (by
                have h_5928 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                (Litex.range _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_14
                      )
                  )
                have h_5929 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_5928).1
                      )
                  )
                have h_5930 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_5928).2.1
                      )
                  )
                have h_5931 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                        let _wd_1_1 := (Litex.add (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                        (Litex.range _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((3 : ℂ) + (2 : ℂ)) (5 : ℤ) (by norm_num)))))) _value_i1 h_5928).2.2
                      )
                  )
                have h_5932 : Litex.Same _value_i1 (Litex.number (M := M) (4 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _enumerated_case
                      )
                  )
                let _object_w28 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_5929) (Litex.integerToComplex _value_i1 h_5929))

                have h_3 : (by
                  let _atomic_wd_1_0 := _object_w28
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w28
                          exact (Litex.leOfSame (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ))) _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (Litex.number (M := M) (16 : ℂ)) ((congrArg₂ M.mulValue h_5932 h_5932)).symm (Litex.sameRefl (Litex.number (M := M) (16 : ℂ))) (by
                            let _atomic_wd_2_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
                            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (16 : ℂ)) (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num)))) = (16 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := _atomic_wd_2_0
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                      )
                  )
                have h_8679 : (by
                  let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
                  exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num)))) = (16 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num)) = (16 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (16 : ℂ) (16 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                      )
                  )
                have h_8732 : Litex.In (Litex.number (M := M) (16 : ℂ)) (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ))) (Litex.number (M := M) (16 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (16 : ℂ) (16 : ℤ) (by norm_num)) (by
                          let _atomic_wd_1_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
                          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num))))).mpr (by
                            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num)))) = (16 : ℝ) := by
                              apply Complex.ofReal_injective
                              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) * (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) * (4 : ℂ)) (16 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_8679)
                      )
                  )
                show (∃ (_r _s : ℝ), (M.mulValue (Litex.denote _value_i1) (Litex.denote _value_i1)) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
                exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (∃ (_r _s : ℝ), (M.mulValue _enumeration_value _enumeration_value) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _enumerated_case) (show (∃ (_r _s : ℝ), (M.mulValue (M.number (4 : ℂ)) (M.number (4 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (16 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) from h_8679)
              )
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_calculated_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit
