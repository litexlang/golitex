import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_object_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), Litex.Same _value_i1 _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    have h_1 : Litex.Same _value_i1 _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (show @Eq M.Value _ _ from Eq.refl _)
          )
      )
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_object_x5f_equals_x5f_itself_x2f_statement_x2e_lit
