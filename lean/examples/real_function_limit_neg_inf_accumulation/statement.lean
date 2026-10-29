import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_function_x5f_limit_x5f_neg_x5f_inf_x5f_accumulation_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Lt _value_i2 _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_29 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_32 : ∀ (_value_i4 : Litex.Obj (M := M) M.Value) (h_60 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_61 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt _value_i5 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by

                    exact (show ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_33 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_34 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt _value_i5 _value_i4 from (by
                    intro _Host _rep _bound _bound_member
                    obtain ⟨_input, _input_member, _beyond⟩ := Litex.realInfiniteLimitAccumulation .negative _bound _bound_member
                    exact ⟨_input, _input_member, _beyond⟩
                  ))
                  )
                )
            )
          exact (by
            let _real_base := _value_i1
            have _real_base_member : Litex.In _real_base Litex.R := h_29
            obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
            exact ⟨_real_witness, _real_member, _real_order⟩)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_function_x5f_limit_x5f_neg_x5f_inf_x5f_accumulation_x2f_statement_x2e_lit
