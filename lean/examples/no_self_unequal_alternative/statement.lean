import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_no_x5f_self_x5f_unequal_x5f_alternative_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_5 : ¬ (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_12 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_3 : ((Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))))), ¬ Litex.Same _value_i1 _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_13 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_14 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_3 : ((Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))))), ¬ Litex.Same _value_i1 _value_i1 := (by
            classical
            simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_8 : ((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))))), ¬ Litex.Same _value_i2 _value_i2 from h_13) with ⟨_value_i3, h_16, h_19, h_20⟩
          exact (by
            have _asserted : Litex.Same _value_i3 _value_i3 := (show @Eq M.Value _ _ from Eq.refl _)
            have _denied : ¬ (Litex.Same _value_i3 _value_i3) := h_20
            exact _denied _asserted)
        )
      )
  )

theorem h_35 : ¬ (∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_36 : Litex.In _value_i5 (Litex.R (M := M))), ∃ (h_33 : ((Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ))))), ¬ Litex.Same _value_i5 _value_i5) :=
  (by
    litex_complete =>
      exact (
        (h_5 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_no_x5f_self_x5f_unequal_x5f_alternative_x2f_statement_x2e_lit
