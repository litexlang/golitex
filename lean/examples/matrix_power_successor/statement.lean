import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_successor_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)), (by
  let _equal_wd_1_0 := (let _wd_1_0 := _value_i3;
  let _wd_1_1 := _value_i1;
  let _wd_1_2 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_5) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_3 (by
    let _atomic_wd_1_0 := _wd_1_2
    exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_5 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_18)))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.matrixPower _value_i3 _value_i1 _value_i2 h_3 h_5 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_18));
  let _wd_1_1 := _value_i3;
  let _wd_1_2 := _value_i1;
  let _wd_1_3 := _wd_1_2;
  let _wd_1_4 := _wd_1_3;
  (Litex.matrixMultiply _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 h_3 h_3 h_3 (by
    let _atomic_wd_1_0 := (Litex.matrixPower _wd_1_1 _wd_1_4 _value_i2 h_3 h_5 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
      exact h_18))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixPowerInFnSet _litex_matrix)))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_18)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_18
          have h_4 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_3)
                )
            )
          have h_6 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_5)
                )
            )
          let _object_h19 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)))
          have h_19 : Litex.In _value_i3 _object_h19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3) _object_h19 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3))) h_18)
                )
            )
          have h_304 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_306 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_319 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_305 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_304)
                )
            )
          have h_307 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_306)
                )
            )
          let _object_h320 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)))
          have h_320 : Litex.In _value_i3 _object_h320 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304) _object_h320 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304))) h_319)
                )
            )
          have h_325 : Litex.Same (let _wd_1_0 := _value_i3;
          let _wd_1_1 := _value_i1;
          let _wd_1_2 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_306) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_304 (by
            let _atomic_wd_1_0 := _wd_1_2
            exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_306 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
            exact h_319))) (let _wd_1_0 := (Litex.matrixPower _value_i3 _value_i1 _value_i2 h_304 h_306 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
            exact h_319));
          let _wd_1_1 := _value_i3;
          let _wd_1_2 := _value_i1;
          let _wd_1_3 := _wd_1_2;
          let _wd_1_4 := _wd_1_3;
          (Litex.matrixMultiply _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 h_304 h_304 h_304 (by
            let _atomic_wd_1_0 := (Litex.matrixPower _wd_1_1 _wd_1_4 _value_i2 h_304 h_306 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
              exact h_319))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixPowerInFnSet _litex_matrix)))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
            exact h_319))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_321 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_304
                          )
                      )
                    have h_330 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_321)
                          )
                      )
                    have h_322 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_321
                          )
                      )
                    have h_335 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_322)
                          )
                      )
                    have h_323 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                              exact h_319)
                          )
                      )
                    let _object_h348 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)))
                    have h_348 : Litex.In _value_i3 _object_h348 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304) _object_h348 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304))) h_323)
                          )
                      )
                    have h_324 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_306
                          )
                      )
                    have h_363 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_324)
                          )
                      )
                    exact (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := _value_i3;
                    let _wd_1_1 := _value_i1;
                    let _wd_1_2 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_324) (Litex.numberInC (M := M) (1 : ℂ)));
                    (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_321 (by
                      let _atomic_wd_1_0 := _wd_1_2
                      exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_324 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                      exact h_323)))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.matrixPower _value_i3 _value_i1 _value_i2 h_321 h_324 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                      exact h_323));
                    let _wd_1_1 := _value_i3;
                    let _wd_1_2 := _value_i1;
                    let _wd_1_3 := _wd_1_2;
                    let _wd_1_4 := _wd_1_3;
                    (Litex.matrixMultiply _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 h_321 h_321 h_321 (by
                      let _atomic_wd_1_0 := (Litex.matrixPower _wd_1_1 _wd_1_4 _value_i2 h_321 h_324 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                        exact h_323))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixPowerInFnSet _litex_matrix)))) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                      exact h_323)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from by
                    let _power := (let _wd_1_0 := _value_i3;
                  let _wd_1_1 := _value_i1;
                  let _wd_1_2 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_324) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_321 (by
                    let _atomic_wd_1_0 := _wd_1_2
                    exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_324 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_304 h_304)
                    exact h_323)))
                    exact Litex.matrixPowerSuccessor _power.val.matrix _power.val.order _power.val.exponent.val.left h_324
                  )
                  )
                )
            )
          exact h_325
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_successor_x2f_statement_x2e_lit
