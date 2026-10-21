import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_set_x5f_laws_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

theorem h_2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.IsSet _value_i1 :=
  h_1

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Same _value_i1 _value_i1 :=
  (show @Eq M.Value _ _ from Eq.refl _)
end LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_set_x5f_laws_x2f_statement_x2e_lit
