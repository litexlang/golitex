import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_is_x5f_complex_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))), Litex.In _value_i1 (Litex.C (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    have h_1 : Litex.In _value_i1 (Litex.C (M := M)) :=
      (Litex.realToComplex _value_i1 h_15)
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_is_x5f_complex_x2f_statement_x2e_lit
