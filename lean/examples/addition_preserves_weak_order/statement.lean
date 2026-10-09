import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_addition_x5f_preserves_x5f_weak_x5f_order_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (_h_param_i3 : Litex.In _value_i3 (Litex.R (M := M))) (_h_dom_f1 : Litex.Le _value_i1 _value_i2), Litex.Le (Litex.add _value_i1 _value_i3 (Litex.realToComplex _value_i1 _h_param_i1) (Litex.realToComplex _value_i3 _h_param_i3)) (Litex.add _value_i2 _value_i3 (Litex.realToComplex _value_i2 _h_param_i2) (Litex.realToComplex _value_i3 _h_param_i3)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2 _Host_i3 _rep_i3 _value_i3 _h_param_i3 _h_dom_f1
    exact (Litex.leAddRight _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 _h_param_i1) (Litex.realToComplex _value_i2 _h_param_i2) (Litex.realToComplex _value_i3 _h_param_i3) _h_param_i3 _h_dom_f1)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_addition_x5f_preserves_x5f_weak_x5f_order_x2f_statement_x2e_lit
