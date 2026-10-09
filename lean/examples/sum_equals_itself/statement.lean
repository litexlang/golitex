import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_27 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_28 : Litex.In _value_i2 (Litex.C (M := M))), Litex.Same (Litex.add _value_i1 _value_i2 h_27 h_28) (Litex.add _value_i1 _value_i2 h_27 h_28) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_27 _Host_i2 _rep_i2 _value_i2 h_28
    have h_1 : Litex.Same (Litex.add _value_i1 _value_i2 h_27 h_28) (Litex.add _value_i1 _value_i2 h_27 h_28) :=
      (Litex.sameRefl (Litex.add _value_i1 _value_i2 h_27 h_28))
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_equals_x5f_itself_x2f_statement_x2e_lit
