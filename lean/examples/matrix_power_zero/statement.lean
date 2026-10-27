import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_zero_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)), (by
  let _equal_wd_1_0 := (Litex.matrixPower _value_i2 _value_i1 (Litex.number (M := M) (0 : ℂ)) h_3 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_16))
  let _equal_wd_1_1 := (Litex.identityMatrix _value_i1 h_3)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3 _Host_i2 _rep_i2 _value_i2 h_16
          have h_4 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_3)
                )
            )
          let _object_h17 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)))
          have h_17 : Litex.In _value_i2 _object_h17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3) _object_h17 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3))) h_16)
                )
            )
          have h_42 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_55 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_43 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_42)
                )
            )
          let _object_h56 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)))
          have h_56 : Litex.In _value_i2 _object_h56 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42) _object_h56 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42))) h_55)
                )
            )
          have h_60 : Litex.Same (Litex.matrixPower _value_i2 _value_i1 (Litex.number (M := M) (0 : ℂ)) h_42 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)
            exact h_55)) (Litex.identityMatrix _value_i1 h_42) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_57 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_42
                          )
                      )
                    have h_65 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_57)
                          )
                      )
                    have h_58 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_57
                          )
                      )
                    have h_70 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_58)
                          )
                      )
                    have h_59 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)
                              exact h_55)
                          )
                      )
                    let _object_h81 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)))
                    have h_81 : Litex.In _value_i2 _object_h81 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42) _object_h81 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42))) h_59)
                          )
                      )
                    exact (show (by
                    let _equal_wd_1_0 := (Litex.matrixPower _value_i2 _value_i1 (Litex.number (M := M) (0 : ℂ)) h_57 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)
                      exact h_59))
                    let _equal_wd_1_1 := (Litex.identityMatrix _value_i1 h_57)
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from by
                    let _power := (Litex.matrixPower _value_i2 _value_i1 (Litex.number (M := M) (0 : ℂ)) h_57 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_42 h_42)
                    exact h_59))
                    exact Litex.matrixPowerZero _power.val.matrix _power.val.order
                  )
                  )
                )
            )
          exact h_60
        )
      )
  )

theorem h_180 : (by
  have h_181 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  have h_182 : (by
    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181)
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
    (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_181 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
      let _atomic_wd_1_0 := _wd_1_0
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
      exact h_182)))
    let _equal_wd_1_1 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_181)
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_181 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_184 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_181)
                )
            )
          have h_182 : (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181)
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
                )
            )
          let _object_h210 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)))
          have h_210 : Litex.In (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181) _object_h210 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181) (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181) (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181) _object_h210 (Litex.sameRefl (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181)) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181))) h_182)
                )
            )
          have h_183 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
          (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_181 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
            exact h_182))) (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_181) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_181 (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181) h_182)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_181 h_181);
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
        (Litex.matrixPower _wd_1_0 _wd_1_1 _wd_1_2 h_181 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
          let _atomic_wd_1_0 := _wd_1_0
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_181 h_181)
          exact h_182)));
        let _equal_wd_1_1 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_181);
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_183).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_zero_x2f_statement_x2e_lit
