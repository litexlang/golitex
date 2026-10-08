import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.C (M := M))) (_h_dom_f1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.div _value_i1 _value_i2 _h_param_i1 _h_param_i2 _h_dom_f1) (Litex.div _value_i1 _value_i2 _h_param_i1 _h_param_i2 _h_dom_f1) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2 _h_dom_f1
    exact (Litex.sameRefl (Litex.div _value_i1 _value_i2 _h_param_i1 _h_param_i2 _h_dom_f1))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_equals_x5f_itself_x2f_statement_x2e_lit
