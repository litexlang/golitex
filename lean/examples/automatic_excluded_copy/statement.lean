import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_excluded_x5f_copy_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (Litex.R (M := M))), ¬ (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i2 _value_i1), ¬ Litex.Same _value_i2 _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12
          have h_14 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_7 : ¬ (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (h_5 : Litex.Same _value_i3 _value_i1), ¬ Litex.Same _value_i3 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_16 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_17 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (h_5 : Litex.Same _value_i3 _value_i1), ¬ Litex.Same _value_i3 _value_i1 := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    rcases (show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_18 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_8 : Litex.Same _value_i4 _value_i1), ¬ Litex.Same _value_i4 _value_i1 from h_16) with ⟨_value_i5, h_19, h_20, h_21⟩
                    exact (by
                      have _asserted : Litex.Same _value_i5 _value_i1 := h_20
                      have _denied : ¬ (Litex.Same _value_i5 _value_i1) := h_21
                      exact _denied _asserted)
                  )
                )
            )

          have h_34 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i7) = (Litex.denote _value_i1)))) ∨ (((Litex.denote _value_i7) = (Litex.denote _value_i1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7
                    have _excluded : ¬ ((∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)), ∃ (h_5 : ((Litex.denote _value_i3) = (Litex.denote _value_i1))), (¬ ((Litex.denote _value_i3) = (Litex.denote _value_i1))))) := h_7
                    have _no_body : ¬ (((((Litex.denote _value_i7) = (Litex.denote _value_i1))) ∧ ((¬ ((Litex.denote _value_i7) = (Litex.denote _value_i1)))))) := by
                      intro _candidate
                      rcases _candidate with ⟨h_5, h_6⟩
                      apply _excluded
                      exact ⟨Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7), _membership_i7, h_5, h_6⟩
                    simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
                )
            )
          exact h_7
        )
      )
  )

theorem h_40 : ¬ (∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_41 : Litex.In _value_i8 (Litex.R (M := M))), ∃ (h_38 : Litex.Same _value_i8 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i8 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_51 : Litex.In (Litex.number (M := M) (7 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))
          intro _exist_candidate
          rcases _exist_candidate with ⟨_value_i8, h_41, h_38, h_39⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
          have _exist_match_2 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
          exact (((h_4 (M := M)) (Litex.number (M := M) (7 : ℂ)) h_51)) ⟨_value_i8, h_41, h_38, h_39⟩
        )
      )
  )

theorem h_57 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i9) = (M.number (7 : ℂ))))) ∨ (((Litex.denote _value_i9) = (M.number (7 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i9 _rep_i9 _value_i9 _membership_i9
          have _excluded : ¬ ((∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)), ∃ (h_38 : ((Litex.denote _value_i8) = (M.number (7 : ℂ)))), (¬ ((Litex.denote _value_i8) = (M.number (7 : ℂ)))))) := (h_40 (M := M))
          have _no_body : ¬ (((((Litex.denote _value_i9) = (M.number (7 : ℂ)))) ∧ ((¬ ((Litex.denote _value_i9) = (M.number (7 : ℂ))))))) := by
            intro _candidate
            rcases _candidate with ⟨h_38, h_39⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9), _membership_i9, h_38, h_39⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_excluded_x5f_copy_x2f_statement_x2e_lit
