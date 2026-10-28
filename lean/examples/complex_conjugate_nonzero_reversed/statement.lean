import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_conjugate_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.conj _value_i1 h_5) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          have h_12 : Litex.In _value_i1 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w5 := (Litex.conj _value_i1 h_12)

          have h_4 : (by
            let _atomic_wd_1_1 := _object_w5
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w5
                    exact (fun _litex_equal => (Litex.conjugateNonzeroOfArg _atomic_wd_1_1 h_1) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w5
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_conjugate_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit
