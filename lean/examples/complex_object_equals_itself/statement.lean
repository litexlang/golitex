import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_object_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M))), Litex.Same _value_i1 _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1
    exact (Litex.sameRefl _value_i1)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_object_x5f_equals_x5f_itself_x2f_statement_x2e_lit
