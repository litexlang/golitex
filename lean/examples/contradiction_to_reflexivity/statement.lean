import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_to_x5f_reflexivity_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_7 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i1) = (Litex.denote _value_i1)))) := (by
            classical
            intro _canonical
            apply _litex_negated_goal
            intro _Host_i1 _rep_i1 _value_i1 h_6
            exact _canonical (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_6)
          have h_10 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i1)))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_7
                    exact _counterexample)
                )
            )
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), ¬ Litex.Same _value_i2 _value_i2 from h_10) with ⟨_value_i3, h_12, h_13⟩
          exact (by
            have _asserted : Litex.Same _value_i3 _value_i3 := (show @Eq M.Value _ _ from Eq.refl _)
            have _denied : ¬ (Litex.Same _value_i3 _value_i3) := h_13
            exact _denied _asserted)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_to_x5f_reflexivity_x2f_statement_x2e_lit
