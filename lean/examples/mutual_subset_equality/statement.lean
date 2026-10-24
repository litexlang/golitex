import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_mutual_x5f_subset_x5f_equality_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.IsSet _value_i2) (h_1 : Litex.Subset _value_i1 _value_i2) (h_2 : Litex.Subset _value_i2 _value_i1), Litex.Same _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 h_1 h_2
          have h_15 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_16 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_24 : Litex.Same _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _extension_forward : Litex.Subset _value_i1 _value_i2 := h_1
                    have _extension_reverse : Litex.Subset _value_i2 _value_i1 := h_2
                    exact Litex.SetSemantics.ext _ _ (Litex.isSet _value_i1) (Litex.isSet _value_i2) (fun x => ⟨_extension_forward x, _extension_reverse x⟩)
                  )
                )
            )
          exact h_24
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_mutual_x5f_subset_x5f_equality_x2f_statement_x2e_lit
