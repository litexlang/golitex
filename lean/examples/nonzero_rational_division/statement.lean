import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_division_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.Q (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.Q (M := M))) (_h_dom_f1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.div _value_i1 _value_i2 (Litex.rationalToComplex _value_i1 _h_param_i1) (Litex.rationalToComplex _value_i2 _h_param_i2) _h_dom_f1) (Litex.Q (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2 _h_dom_f1
    exact (Litex.divInQ _value_i1 _value_i2 _h_param_i1 _h_param_i2 ((Litex.div _value_i1 _value_i2 (Litex.rationalToComplex _value_i1 _h_param_i1) (Litex.rationalToComplex _value_i2 _h_param_i2) _h_dom_f1)).wd.2.2)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_division_x2f_statement_x2e_lit
