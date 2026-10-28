import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_lcm_x5f_nonzero_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.Z (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.lcm _value_i1 _value_i2 h_6 h_7) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 h_1 h_2
          have h_23 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_24 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          let _object_w5 := (Litex.lcm _value_i1 _value_i2 h_23 h_24)

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w5
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (fun _litex_equal => (Litex.lcmNonzeroOfArgs _atomic_wd_1_0 h_1 h_2) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w5
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_lcm_x5f_nonzero_x2f_statement_x2e_lit
