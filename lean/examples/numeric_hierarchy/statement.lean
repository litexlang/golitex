import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_hierarchy_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.N (M := M))), Litex.In _value_i1 (Litex.Z (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (Litex.naturalNonnegative _value_i1 h_15)
    have h_1 : Litex.In _value_i1 (Litex.Z (M := M)) :=
      (Litex.naturalToInteger _value_i1 h_15)
    exact h_1
  )

theorem h_43 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_56 : Litex.In _value_i2 (Litex.Z (M := M))), Litex.In _value_i2 (Litex.Q (M := M)) :=
  (by
    intro _Host_i2 _rep_i2 _value_i2 h_56
    have h_42 : Litex.In _value_i2 (Litex.Q (M := M)) :=
      (Litex.integerToRational _value_i2 h_56)
    exact h_42
  )

theorem h_67 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_80 : Litex.In _value_i3 (Litex.Q (M := M))), Litex.In _value_i3 (Litex.R (M := M)) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_80
    have h_66 : Litex.In _value_i3 (Litex.R (M := M)) :=
      (Litex.rationalToReal _value_i3 h_80)
    exact h_66
  )

theorem h_91 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_104 : Litex.In _value_i4 (Litex.R (M := M))), Litex.In _value_i4 (Litex.C (M := M)) :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_104
    have h_90 : Litex.In _value_i4 (Litex.C (M := M)) :=
      (Litex.realToComplex _value_i4 h_104)
    exact h_90
  )
end LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_hierarchy_x2f_statement_x2e_lit
