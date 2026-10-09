import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_hierarchy_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.N (M := M))), Litex.In _value_i1 (Litex.Z (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1
    exact (Litex.naturalToInteger _value_i1 _h_param_i1)
  )

theorem fact_2 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.Z (M := M))), Litex.In _value_i2 (Litex.Q (M := M)) :=
  (by
    intro _Host_i2 _rep_i2 _value_i2 _h_param_i2
    exact (Litex.integerToRational _value_i2 _h_param_i2)
  )

theorem fact_3 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (_h_param_i3 : Litex.In _value_i3 (Litex.Q (M := M))), Litex.In _value_i3 (Litex.R (M := M)) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 _h_param_i3
    exact (Litex.rationalToReal _value_i3 _h_param_i3)
  )

theorem fact_4 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_h_param_i4 : Litex.In _value_i4 (Litex.R (M := M))), Litex.In _value_i4 (Litex.C (M := M)) :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 _h_param_i4
    exact (Litex.realToComplex _value_i4 _h_param_i4)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_hierarchy_x2f_statement_x2e_lit
