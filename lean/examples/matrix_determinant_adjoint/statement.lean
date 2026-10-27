import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_adjoint_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.conjugateTranspose _value_i2 _value_i1 _value_i1 h_3 h_3 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_16));
  let _wd_1_1 := _value_i1;
  (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_3 (by
    let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i2 _wd_1_1 _wd_1_1 h_3 h_3 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
      exact h_16))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_3 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact h_16));
  (Litex.conj _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_3 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
      exact h_16))
    exact (Litex.matrixDeterminantInC _atomic_wd_1_0))))
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
          have h_186 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_199 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_187 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_186)
                )
            )
          let _object_h200 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)))
          have h_200 : Litex.In _value_i2 _object_h200 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186) _object_h200 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186))) h_199)
                )
            )
          have h_204 : Litex.Same (let _wd_1_0 := (Litex.conjugateTranspose _value_i2 _value_i1 _value_i1 h_186 h_186 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
            exact h_199));
          let _wd_1_1 := _value_i1;
          (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_186 (by
            let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i2 _wd_1_1 _wd_1_1 h_186 h_186 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
              exact h_199))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix)))))) (let _wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_186 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
            exact h_199));
          (Litex.conj _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_186 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
              exact h_199))
            exact (Litex.matrixDeterminantInC _atomic_wd_1_0)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_201 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_186
                          )
                      )
                    have h_209 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_201)
                          )
                      )
                    have h_202 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_201
                          )
                      )
                    have h_214 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_202)
                          )
                      )
                    have h_203 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                              exact h_199)
                          )
                      )
                    let _object_h225 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)))
                    have h_225 : Litex.In _value_i2 _object_h225 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186) _object_h225 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186))) h_203)
                          )
                      )
                    exact (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.conjugateTranspose _value_i2 _value_i1 _value_i1 h_201 h_201 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                      exact h_203));
                    let _wd_1_1 := _value_i1;
                    (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_201 (by
                      let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i2 _wd_1_1 _wd_1_1 h_201 h_201 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                        exact h_203))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_201 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                      exact h_203));
                    (Litex.conj _wd_1_0 (by
                      let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_201 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                        exact h_203))
                      exact (Litex.matrixDeterminantInC _atomic_wd_1_0))))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from by
                    let _det := (let _wd_1_0 := (Litex.conjugateTranspose _value_i2 _value_i1 _value_i1 h_201 h_201 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                    exact h_203));
                  let _wd_1_1 := _value_i1;
                  (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_201 (by
                    let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i2 _wd_1_1 _wd_1_1 h_201 h_201 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                      exact h_203))
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_186 h_186)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))))
                    exact Litex.matrixDeterminantAdjoint _det.val.matrix.val.matrix _det.val.order _det.wd.1 _det.val.matrix.wd.2.2
                  )
                  )
                )
            )
          exact h_204
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_adjoint_x2f_statement_x2e_lit
