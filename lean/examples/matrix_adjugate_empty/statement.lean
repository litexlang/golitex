import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_empty_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
(Litex.matrixAdjugate _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))))

noncomputable def _object_w7 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  let _atomic_wd_1_1 := (_object_w7 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w6 (M := M))
          let _atomic_wd_1_1 := (_object_w7 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixAdjugateInFnSet _litex_matrix))))
      )
  )

noncomputable def _object_h31 := (Litex.fnSet (Litex.matrixSignature (_object_w7 (M := M))))

theorem h_31 : Litex.In (_object_w6 (M := M)) (_object_h31 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_w6 (M := M)) (_object_w6 (M := M)) (_object_w7 (M := M)) (_object_h31 (M := M)) (Litex.sameRefl (_object_w6 (M := M))) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (_object_w7 (M := M)))) (h_1 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_empty_x2f_statement_x2e_lit
