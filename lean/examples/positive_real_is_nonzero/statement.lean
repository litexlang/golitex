import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_is_x5f_nonzero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    have h_2 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _value_i1 h_1) _litex_equal.symm)
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_is_x5f_nonzero_x2f_statement_x2e_lit
