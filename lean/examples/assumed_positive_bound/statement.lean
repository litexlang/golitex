import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_positive_x5f_bound_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

variable (h_3 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)

theorem h_12 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) (h_3 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _value_i1 h_3)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_positive_x5f_bound_x2f_statement_x2e_lit
