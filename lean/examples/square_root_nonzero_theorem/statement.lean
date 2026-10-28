import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_root_x5f_nonzero_x5f_theorem_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), ¬ Litex.Same (Litex.sqrt _value_i1 h_5 (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _value_i1 h_1)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          have h_33 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w5 := (Litex.sqrt _value_i1 h_33 (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _value_i1 h_1))

          have h_4 : (by
            let _atomic_wd_1_0 := _object_w5
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (fun _litex_equal => (Litex.sqrtNonzeroOfPositive _atomic_wd_1_0 h_1) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w5
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_root_x5f_nonzero_x5f_theorem_x2f_statement_x2e_lit
