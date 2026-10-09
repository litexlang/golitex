import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_is_x5f_nonzero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.R (M := M))) (_h_dom_f1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _h_dom_f1
    exact (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _value_i1 _h_dom_f1) _litex_equal.symm)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_real_x5f_is_x5f_nonzero_x2f_statement_x2e_lit
