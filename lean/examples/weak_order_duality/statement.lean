import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_order_x5f_duality_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), Litex.Le _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 h_1
          have h_2 : Litex.Le _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_order_x5f_duality_x2f_statement_x2e_lit
