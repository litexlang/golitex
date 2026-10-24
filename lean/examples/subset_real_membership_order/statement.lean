import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_subset_x5f_real_x5f_membership_x5f_order_x2f_statement_x2e_lit

universe u v1 v2 v4 v5
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 _value_i1) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))), Litex.In _value_i2 (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1
          have h_2 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1 (Litex.denote _value_i2) h_6)
                )
            )
          exact h_2
        )
      )
  )

theorem h_39 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_43 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_44 : Litex.In _value_i5 _value_i4) (h_37 : Litex.Subset _value_i4 (Litex.R (M := M))), Litex.Le _value_i5 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_43 _Host_i5 _rep_i5 _value_i5 h_44 h_37
          have h_38 : Litex.Le _value_i5 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leRefl _value_i5 (h_37 (Litex.denote _value_i5) h_44))
                )
            )
          exact h_38
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_subset_x5f_real_x5f_membership_x5f_order_x2f_statement_x2e_lit
