import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_quantified_x5f_premise_x5f_host_x5f_bridge_x2f_statement_x2e_lit

universe u v4 v5 v6
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 2 → M.Value) → Prop)

theorem h_6 (abstract_prop_1 : (Fin 2 → M.Value) → Prop) : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_7 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_8 : Litex.In _value_i5 _value_i4) (h_3 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_9 : Litex.In _value_i6 _value_i4), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_10 : Litex.In _value_i7 _value_i4), (abstract_prop_1 ![(Litex.denote _value_i6), (Litex.denote _value_i7)])), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i8 _value_i4), (abstract_prop_1 ![(Litex.denote _value_i5), (Litex.denote _value_i8)]) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_7 _Host_i5 _rep_i5 _value_i5 h_8 h_3
          have h_12 : Litex.IsSet _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_13 : Litex.In _value_i5 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          exact (by
            have h_22 : Litex.In _value_i5 _value_i4 :=
              h_13
            rcases (h_3 (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) h_22) with ⟨_value_i8, h_16, h_4⟩
            have _exist_match_0 : Litex.Same _value_i4 _value_i4 := (Litex.sameRefl _value_i4)
            have _exist_match_1 : Litex.Same _value_i5 _value_i5 := (Litex.sameRefl _value_i5)
            exact ⟨_value_i8, h_16, h_4⟩
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_quantified_x5f_premise_x5f_host_x5f_bridge_x2f_statement_x2e_lit
