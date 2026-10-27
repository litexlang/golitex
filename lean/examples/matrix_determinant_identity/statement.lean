import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_identity_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix _value_i1 h_3);
  let _wd_1_1 := _value_i1;
  (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_3 (by
    let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_3)
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_3 h_3)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3
          have h_4 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_3)
                )
            )
          have h_36 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_37 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_36)
                )
            )
          have h_39 : Litex.Same (let _wd_1_0 := (Litex.identityMatrix _value_i1 h_36);
          let _wd_1_1 := _value_i1;
          (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_36 (by
            let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_36)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_36 h_36)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_38 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_36
                          )
                      )
                    have h_44 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_38)
                          )
                      )
                    exact (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix _value_i1 h_38);
                    let _wd_1_1 := _value_i1;
                    (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_38 (by
                      let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_38)
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_38 h_38)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
                    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) from by
                    let _det := (let _wd_1_0 := (Litex.identityMatrix _value_i1 h_38);
                  let _wd_1_1 := _value_i1;
                  (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_38 (by
                    let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_38)
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_38 h_38)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
                    exact Litex.matrixDeterminantIdentity _det.val.order _det.wd.1
                  )
                  )
                )
            )
          exact h_39
        )
      )
  )

theorem h_145 : (by
  have h_146 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_146);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_146 (by
      let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_146)
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_146 h_146)
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_146 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_148 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_146)
                )
            )
          have h_147 : Litex.Same (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_146);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_146 (by
            let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_146)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_146 h_146)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_146)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) h_146);
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.matrixDeterminant _wd_1_0 _wd_1_1 h_146 (by
          let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_1 h_146)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_146 h_146)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_147).trans (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_identity_x2f_statement_x2e_lit
