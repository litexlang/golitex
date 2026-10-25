import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_nonzero_x5f_denominator_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

variable (h_3 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)))

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) (h_3 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_2) h_3)

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) (h_3 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) : (by
  let _equal_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (h_3 := h_3))
  let _equal_wd_1_1 := _equal_wd_1_0
  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (show @Eq M.Value _ _ from Eq.refl _)
      )
  )

theorem h_42 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) (h_3 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) : Litex.In _value_i1 (Litex.C (M := M)) :=
  (by
    litex_complete =>
      exact (
        (M.real_subset_complex _ h_2)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_nonzero_x5f_denominator_x2f_statement_x2e_lit
