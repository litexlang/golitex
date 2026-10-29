import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sqrt_x5f_monotone_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1) (h_2 : Litex.Le _value_i1 _value_i2), Litex.Le (Litex.sqrt _value_i1 h_6 h_1) (Litex.sqrt _value_i2 h_7 (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 _value_i2 h_1 h_2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 h_1 h_2
          have h_517 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_518 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          let _object_w5 := (Litex.sqrt _value_i1 h_517 h_1)

          let _object_w6 := (Litex.sqrt _value_i2 h_518 (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 _value_i2 h_1 h_2))

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (Litex.sqrtMonotone _atomic_wd_1_0 _atomic_wd_1_1 h_2))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sqrt_x5f_monotone_x2f_statement_x2e_lit
