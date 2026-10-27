import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_zero_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.In _value_i2 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix _value_i1 _value_i2 h_3 h_5);
  let _wd_1_1 := _value_i1;
  let _wd_1_2 := _value_i2;
  (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_3 h_5 (by
    let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_3 h_5)
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_3 h_5)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3 _Host_i2 _rep_i2 _value_i2 h_5
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
          have h_65 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3
                )
            )
          have h_67 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_66 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_65)
                )
            )
          have h_68 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_67)
                )
            )
          have h_71 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix _value_i1 _value_i2 h_65 h_67);
          let _wd_1_1 := _value_i1;
          let _wd_1_2 := _value_i2;
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_65 h_67 (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_65 h_67)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_65 h_67)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_69 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_65
                          )
                      )
                    have h_76 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_69)
                          )
                      )
                    have h_70 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_67
                          )
                      )
                    have h_85 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_70)
                          )
                      )
                    exact (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix _value_i1 _value_i2 h_69 h_70);
                    let _wd_1_1 := _value_i1;
                    let _wd_1_2 := _value_i2;
                    (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_69 h_70 (by
                      let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_69 h_70)
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_69 h_70)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
                    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) from by
                    let _rank := (let _wd_1_0 := (Litex.zeroMatrix _value_i1 _value_i2 h_69 h_70);
                  let _wd_1_1 := _value_i1;
                  let _wd_1_2 := _value_i2;
                  (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_69 h_70 (by
                    let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_69 h_70)
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_69 h_70)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
                    exact Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1
                  )
                  )
                )
            )
          exact h_71
        )
      )
  )

theorem h_273 : (by
  have h_274 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  have h_275 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_274 h_275);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
    (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_274 h_275 (by
      let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_274 h_275)
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_274 h_275)
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_274 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_277 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_274)
                )
            )
          have h_275 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
                )
            )
          have h_280 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (3 : ℂ)) h_275)
                )
            )
          have h_276 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_274 h_275);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_274 h_275 (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_274 h_275)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_274 h_275)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_274 (Litex.number (M := M) (3 : ℂ)) h_275)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_274 h_275);
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_274 h_275 (by
          let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_274 h_275)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_274 h_275)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_276).trans (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_zero_x2f_statement_x2e_lit
