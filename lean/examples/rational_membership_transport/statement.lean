import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_membership_x5f_transport_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : Litex.Same _value_i1 _value_i2) (h_2 : Litex.In _value_i1 (Litex.Q (M := M))), Litex.In _value_i2 (Litex.Q (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 h_1 h_2
    have h_3 : Litex.In _value_i2 (Litex.Q (M := M)) :=
      (Litex.inOfSame _value_i1 _value_i2 (Litex.Q (M := M)) (Litex.Q (M := M)) (((Litex.sameRefl _value_i1)).trans h_1) (Litex.sameRefl (Litex.Q (M := M))) h_2)
    exact h_3
  )
end LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_membership_x5f_transport_x2f_statement_x2e_lit
