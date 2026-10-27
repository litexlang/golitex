import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_empty_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
(Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
                )
            )
          have h_4 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_1)
                )
            )
          have h_2 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
                )
            )
          have h_7 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (3 : ℂ)) h_2)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_1 h_2);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_1 h_2 (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_1 h_2)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_1 h_2)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) from by
          let _rank := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_1 h_2);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_1 h_2 (by
          let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_1 h_2)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_1 h_2)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1
        )
        )
      )
  )

theorem h_78 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
(Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (3 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (3 : ℂ)) _wd_1_2 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_76 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
                )
            )
          have h_79 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (3 : ℂ)) h_76)
                )
            )
          have h_77 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
                )
            )
          have h_82 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_77)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_76 h_77);
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_76 h_77 (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_76 h_77)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_76 h_77)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) from by
          let _rank := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_76 h_77);
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.number (M := M) (0 : ℂ));
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_76 h_77 (by
          let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_1 _wd_1_2 h_76 h_77)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_76 h_77)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1
        )
        )
      )
  )

theorem h_153 : Litex.Same (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
let _wd_1_2 := _wd_1_1;
(Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_2 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_151 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
                )
            )
          have h_154 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_151)
                )
            )
          have h_152 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_151
                )
            )
          have h_159 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_152)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_151 h_151);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := _wd_1_1;
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_151 h_151 (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_2 _wd_1_2 h_151 h_151)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_151 h_151)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) from by
          let _rank := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_151 h_151);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        let _wd_1_2 := _wd_1_1;
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_151 h_151 (by
          let _atomic_wd_1_0 := (Litex.zeroMatrix _wd_1_2 _wd_1_2 h_151 h_151)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_151 h_151)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
          exact Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1
        )
        )
      )
  )

theorem h_221 : Litex.Same (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
let _wd_1_2 := _wd_1_1;
(Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_220 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
                )
            )
          have h_222 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_220)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (0 : ℂ)) h_220);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := _wd_1_1;
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_220 h_220 (by
            let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_2 h_220)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_220 h_220)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) from by
          let _rank := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (0 : ℂ)) h_220);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        let _wd_1_2 := _wd_1_1;
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_220 h_220 (by
          let _atomic_wd_1_0 := (Litex.identityMatrix _wd_1_2 h_220)
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_220 h_220)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
          exact Litex.matrixRankIdentity _rank.val.rows _rank.wd.1
        )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_empty_x2f_statement_x2e_lit
