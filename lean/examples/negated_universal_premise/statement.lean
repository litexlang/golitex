import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_negated_x5f_universal_x5f_premise_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (Litex.R (M := M))) (h_2 : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M)))) → (((Litex.denote _value_i2) = (M.number (0 : ℂ)))))), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 h_2
          have h_13 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_2
                    exact _counterexample)
                )
            )
          have h_14 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_18 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_2
                    exact _counterexample)
                )
            )
          rcases (show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i3 (let _setElement_0 := _value_i1;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) from h_18) with ⟨_value_i4, h_21, h_23⟩

          have h_22 : Litex.Same _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i4) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M))) := h_21
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_7 : Litex.Same _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_8 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.notSameOfSame _value_i4 _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_22 (show @Eq M.Value _ _ from Eq.refl _) h_23)
                )
            )
          exact (Litex.notSameOfSame _value_i4 _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_22 (show @Eq M.Value _ _ from Eq.refl _) h_23)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_negated_x5f_universal_x5f_premise_x2f_statement_x2e_lit
