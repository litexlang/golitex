import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_order_x5f_transitivity_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2) (h_2 : Litex.Le _value_i2 _value_i3), Litex.Le _value_i1 _value_i3 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
    have h_3 : Litex.Le _value_i1 _value_i3 :=
      (Litex.leTrans _value_i1 _value_i2 _value_i3 h_1 h_2)
    exact h_3
  )
end LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_order_x5f_transitivity_x2f_statement_x2e_lit
