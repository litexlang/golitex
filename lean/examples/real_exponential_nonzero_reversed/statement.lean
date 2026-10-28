import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_exponential_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w3 := (Litex.exp _value_i1 h_15)
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w3 := (Litex.exp _value_i1 h_15)
          have h_1 : (by
            let _atomic_wd_1_1 := _object_w3
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (fun _litex_equal => (Litex.expNonzero _atomic_wd_1_1) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_exponential_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit
