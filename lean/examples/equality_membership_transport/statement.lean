import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_membership_x5f_transport_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.C (M := M))) (_h_dom_f1 : Litex.Same _value_i1 _value_i2) (_h_dom_f2 : Litex.In _value_i1 (Litex.R (M := M))), Litex.In _value_i2 (Litex.R (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2 _h_dom_f1 _h_dom_f2
    exact (Litex.inOfSame _value_i1 _value_i2 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i1)).trans _h_dom_f1) (Litex.sameRefl (Litex.R (M := M))) _h_dom_f2)
  )

theorem fact_2 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (_h_param_i3 : Litex.In _value_i3 (Litex.C (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_h_param_i4 : Litex.In _value_i4 (Litex.C (M := M))) (_h_dom_f35 : Litex.Same _value_i3 _value_i4), Litex.Same _value_i4 _value_i3 :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 _h_param_i3 _Host_i4 _rep_i4 _value_i4 _h_param_i4 _h_dom_f35
    exact (((Litex.sameRefl _value_i4)).trans (_h_dom_f35).symm)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_membership_x5f_transport_x2f_statement_x2e_lit
