import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_28 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_29 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.div _value_i1 _value_i2 h_28 h_29 h_1) (Litex.div _value_i1 _value_i2 h_28 h_29 h_1) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_28 _Host_i2 _rep_i2 _value_i2 h_29 h_1
    have h_2 : Litex.Same (Litex.div _value_i1 _value_i2 h_28 h_29 h_1) (Litex.div _value_i1 _value_i2 h_28 h_29 h_1) :=
      (Litex.sameRefl (Litex.div _value_i1 _value_i2 h_28 h_29 h_1))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_equals_x5f_itself_x2f_statement_x2e_lit
