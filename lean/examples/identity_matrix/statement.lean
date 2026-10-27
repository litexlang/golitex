import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.N (M := M))), (by
  let _object_w3 := (Litex.identityMatrix _value_i1 h_15)
  let _object_w4 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.R (M := M))) h_15 h_15)
  exact (by
    let _atomic_wd_1_0 := _object_w3
    let _atomic_wd_1_1 := _object_w4
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_15)
                )
            )
          let _object_w3 := (Litex.identityMatrix _value_i1 h_15)
          let _object_w4 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.R (M := M))) h_15 h_15)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix))))
                )
            )
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature _object_w4))
          have h_37 : Litex.In _object_w3 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w3 _object_w3 _object_w4 _object_h37 (Litex.sameRefl _object_w3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w4)) h_1)
                )
            )
          exact h_1
        )
      )
  )

noncomputable def _object_w6 := (Litex.identityMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))

noncomputable def _object_w7 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))

theorem h_38 : (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  let _atomic_wd_1_1 := (_object_w7 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w6 (M := M))
          let _atomic_wd_1_1 := (_object_w7 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.identityMatrixSignature (_litex_matrix).val.order); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.identityMatrixInFnSet _litex_matrix)))))
      )
  )

noncomputable def _object_h43 := (Litex.fnSet (Litex.matrixSignature (_object_w7 (M := M))))

theorem h_43 : Litex.In (_object_w6 (M := M)) (_object_h43 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_w6 (M := M)) (_object_w6 (M := M)) (_object_w7 (M := M)) (_object_h43 (M := M)) (Litex.sameRefl (_object_w6 (M := M))) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (_object_w7 (M := M)))) (h_38 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_matrix_x2f_statement_x2e_lit
