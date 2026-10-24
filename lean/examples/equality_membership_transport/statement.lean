import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_membership_x5f_transport_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : Litex.Same _value_i1 _value_i2) (h_2 : Litex.In _value_i1 (Litex.R (M := M))), Litex.In _value_i2 (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 h_1 h_2
          have h_3 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i2 (Litex.R (M := M)) (Litex.R (M := M)) h_1 (show @Eq M.Value _ _ from Eq.refl _) h_2)
                )
            )
          exact h_3
        )
      )
  )

theorem h_37 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_50 : Litex.In _value_i3 (Litex.C (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_51 : Litex.In _value_i4 (Litex.C (M := M))) (h_35 : Litex.Same _value_i3 _value_i4), Litex.Same _value_i4 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_50 _Host_i4 _rep_i4 _value_i4 h_51 h_35
          have h_36 : Litex.Same _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (h_35).symm
                )
            )
          exact h_36
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_membership_x5f_transport_x2f_statement_x2e_lit
