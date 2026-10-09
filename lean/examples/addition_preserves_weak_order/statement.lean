import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_addition_x5f_preserves_x5f_weak_x5f_order_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), Litex.Le (Litex.add _value_i1 _value_i3 (Litex.realToComplex _value_i1 h_16) (Litex.realToComplex _value_i3 h_18)) (Litex.add _value_i2 _value_i3 (Litex.realToComplex _value_i2 h_17) (Litex.realToComplex _value_i3 h_18)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18 h_1
    have h_2 : Litex.Le (Litex.add _value_i1 _value_i3 (Litex.realToComplex _value_i1 h_16) (Litex.realToComplex _value_i3 h_18)) (Litex.add _value_i2 _value_i3 (Litex.realToComplex _value_i2 h_17) (Litex.realToComplex _value_i3 h_18)) :=
      (Litex.leAddRight _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 h_16) (Litex.realToComplex _value_i2 h_17) (Litex.realToComplex _value_i3 h_18) h_18 h_1)
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_addition_x5f_preserves_x5f_weak_x5f_order_x2f_statement_x2e_lit
