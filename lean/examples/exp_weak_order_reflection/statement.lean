import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exp_x5f_weak_x5f_order_x5f_reflection_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.exp _value_i1 h_5)
  let _atomic_wd_1_1 := (Litex.exp _value_i2 h_6)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)), Litex.Le _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1
          have h_91 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_92 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_4 : Litex.Le _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.expLeIff (Litex.exp _value_i1 h_91) (Litex.exp _value_i2 h_92)).mp (by
                    let _atomic_wd_2_0 := (Litex.exp _value_i1 h_91)
                    let _atomic_wd_2_1 := (Litex.exp _value_i2 h_92)
                    exact h_1))
                )
            )
          exact h_4
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_exp_x5f_weak_x5f_order_x5f_reflection_x2f_statement_x2e_lit
