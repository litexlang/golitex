import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_universal_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_6 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i1) = (Litex.denote _value_i1)))) := (by
            classical
            intro _canonical
            apply _litex_negated_goal
            intro _Host_i1 _rep_i1 _value_i1 h_5
            exact _canonical (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_5)
          have h_9 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i1)))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_6
                    exact _counterexample)
                )
            )
          exact (by
            have _universal : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i2 := (by
            intro _Host_i2 _rep_i2 _value_i2 h_22
            have h_3 : Litex.Same _value_i2 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            exact h_3
          )
            have _not_universal : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i2) = (Litex.denote _value_i2)))) := (by
            classical
            intro _universal
            have _counterexample : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i2 (Litex.R (M := M))), ¬ Litex.Same _value_i2 _value_i2 := h_9
            rcases _counterexample with ⟨_value_i2, h_27, h_25⟩
            have _positive : ((Litex.denote _value_i2) = (Litex.denote _value_i2)) := _universal _value_i2 h_27
            have _negative : (¬ ((Litex.denote _value_i2) = (Litex.denote _value_i2))) := h_25
            have _refute : ¬ (((Litex.denote _value_i2) = (Litex.denote _value_i2))) := by
              simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
            exact _refute _positive)
            apply _not_universal
            intro _closing_i2 _closing_member_i2
            exact _universal _closing_i2 _closing_member_i2)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_universal_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit
