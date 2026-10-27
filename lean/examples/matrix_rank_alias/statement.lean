import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_alias_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
theorem h_2 : Litex.Same (_object_i1 (M := M)) (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
      )
  )

noncomputable def _object_i2 := (Litex.matrixRank (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_2 (M := M))).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))
theorem h_9 : Litex.Same (_object_i2 (M := M)) (Litex.matrixRank (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_2 (M := M))).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.matrixRank (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
          exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_2 (M := M))).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
      )
  )

theorem h_10 : Litex.In (_object_i2 (M := M)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.matrixRank (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
          exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_2 (M := M))).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))) (_object_i2 (M := M)) (Litex.N (M := M)) (Litex.N (M := M)) ((((Litex.sameRefl (_object_i2 (M := M)))).trans (h_9 (M := M)))).symm (Litex.sameRefl (Litex.N (M := M))) (by
          let _atomic_wd_2_0 := (Litex.matrixRank (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_2 (M := M))).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))
          exact (Litex.matrixRankInN _atomic_wd_2_0)))
      )
  )

theorem h_43 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative (_object_i2 (M := M)) (h_10 (M := M)))
      )
  )

theorem h_45 : Litex.Same (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
(Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := _wd_1_0
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))))) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_44 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_48 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_44)
                )
            )
          exact (show (by
          let _equal_wd_1_0 := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := _wd_1_1;
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_44 h_44 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_44 h_44)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) from by
          let _rank := (let _wd_1_0 := (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := _wd_1_1;
        (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_44 h_44 (by
          let _atomic_wd_1_0 := _wd_1_0
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_44 h_44)
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))))
          exact Litex.matrixRankIdentity _rank.val.rows _rank.wd.1
        )
        )
      )
  )

theorem h_97 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_9 (M := M)) (Eq.trans (@congr M.Value M.Value _ _ _ _ (congrArg₂ (fun a m => Litex.matrixRankValue (M := M) a m) (show Litex.denote (_object_i1 (M := M)) = Litex.denote (Litex.identityMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) from (h_2 (M := M))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))) (h_45 (M := M))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_alias_x2f_statement_x2e_lit
