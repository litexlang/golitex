import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_calculated_x5f_integer_x5f_range_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.range _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num))))))), ((Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          have h_16 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_15).1
                )
            )
          have h_17 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_15).2.1
                )
            )
          have h_18 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_15).2.2
                )
            )
          have h_29 : Litex.In _value_i1 (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.range _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_30 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_29).1
                )
            )
          have h_31 : Litex.Le (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_29).2.1
                )
            )
          have h_32 : Litex.Lt _value_i1 (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num)))))) _value_i1 h_29).2.2
                )
            )
          have h_40 : (Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _expanded_range := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                    (Litex.range _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num))))))
                    obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.inRangeInteger _expanded_range _value_i1 (2 : ℤ) (4 : ℤ) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (2 : ℂ)) = ((4 : ℤ) : ℂ)))) (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                      (Litex.range _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) + (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℤ) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) + (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq ((2 : ℂ) + (2 : ℂ)) (4 : ℤ) (by norm_num))))))
                      exact h_29)
                    have _range_cases : _range_integer = (2 : ℤ) ∨ _range_integer = (3 : ℤ) := by omega
                    rcases _range_cases with _range_case | _range_case
                    · exact (Or.inl (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                    · exact (Or.inr (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                  )
                )
            )
          exact h_40
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_calculated_x5f_integer_x5f_range_x2f_statement_x2e_lit
