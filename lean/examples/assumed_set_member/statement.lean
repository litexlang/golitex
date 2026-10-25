import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_set_x5f_member_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

variable {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1)

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1) : Litex.In _value_i2 _value_i1 :=
  (by
    litex_complete =>
      exact (
        h_2
      )
  )

theorem h_8 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1) : Litex.IsSet _value_i2 :=
  (by
    litex_complete =>
      exact (
        (Litex.isSet _value_i2)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_set_x5f_member_x2f_statement_x2e_lit
