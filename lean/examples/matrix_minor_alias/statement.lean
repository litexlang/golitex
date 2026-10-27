import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_minor_x5f_alias_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
theorem h_3 : Litex.Same (_object_i1 (M := M)) (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
      )
  )

noncomputable def _object_i2 := (Litex.matrixMinor (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_3 (M := M))).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix))))))
theorem h_16 : Litex.Same (_object_i2 (M := M)) (Litex.matrixMinor (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_3 (M := M))).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.matrixMinor (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
          let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
          exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_3 (M := M))).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))
      )
  )

noncomputable def _object_w8 := (let _wd_1_0 := (Litex.C (M := M));
let _wd_1_1 := (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_2 := _wd_1_1;
(Litex.matrixSet _wd_1_0 _wd_1_1 _wd_1_2 (Litex.isSet _wd_1_0) (by
  let _atomic_wd_1_0 := _wd_1_2
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) - (1 : ℂ)) (Litex.N (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) - (1 : ℂ)) (1 : ℕ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_2
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) - (1 : ℂ)) (Litex.N (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) - (1 : ℂ)) (1 : ℕ) (by norm_num))))))

theorem h_17 : (by
  let _atomic_wd_1_1 := (_object_w8 (M := M))
  exact Litex.In (_object_i2 (M := M)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w8 (M := M))
          exact (show Litex.In (_object_i2 (M := M)) _atomic_wd_1_1 from (let _litex_matrix := (Litex.matrixMinor (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact (show Litex.In (_object_i1 (M := M)) _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))); let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix (_object_i1 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_3 (M := M))).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))); let _litex_matrix_signature := (Litex.matrixMinorSignature (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix (_object_i2 (M := M)) (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((h_16 (M := M))).symm (by rfl) (Litex.matrixMinorInFnSet _litex_matrix))))
      )
  )

noncomputable def _object_h44 := (Litex.fnSet (Litex.matrixSignature (_object_w8 (M := M))))

theorem h_44 : Litex.In (_object_i2 (M := M)) (_object_h44 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_i2 (M := M)) (_object_i2 (M := M)) (_object_w8 (M := M)) (_object_h44 (M := M)) (Litex.sameRefl (_object_i2 (M := M))) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (_object_w8 (M := M)))) (h_17 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_minor_x5f_alias_x2f_statement_x2e_lit
