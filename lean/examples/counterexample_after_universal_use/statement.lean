import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_counterexample_x5f_after_x5f_universal_x5f_use_x2f_statement_x2e_lit

universe u v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_3 : Litex.In _value_i1 (Litex.R (M := M))), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_5 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          have h_6 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) := rfl
          have h_7 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          exact ⟨_value_i1, h_5, h_7⟩
      )
  )

theorem h_9 : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i2) = (M.number (0 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_14 : ∀ (_value_i2 : Litex.Obj (M := M) M.Value) (h_15 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := (Classical.byContradiction _litex_negated_goal)
          have h_10 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_29 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
                      (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                    exact (Eq.trans (Eq.symm (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))) (Eq.trans ((show ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) from (fun {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : Litex.In _value_i2 (Litex.R (M := M))) => by
                    exact h_14 (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_15)) (Litex.number (M := M) (1 : ℂ)) h_29) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))))
                  )
                )
            )
          exact (by
            have _universal : ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_36 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) := (by
            intro _Host_i3 _rep_i3 _value_i3 h_36
            exact ((show ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) from (fun {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : Litex.In _value_i2 (Litex.R (M := M))) => by
            exact h_14 (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_15)) _value_i3 h_36)
          )
            have _not_universal : ¬ (∀ (_value_i3 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i3) = (M.number (0 : ℂ))))) := (by
            classical
            intro _universal
            have _counterexample : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i3 (Litex.R (M := M))), ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) := (by
            let _real_base := (Litex.number (M := M) (0 : ℂ))
            have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
            obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
            exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
            rcases _counterexample with ⟨_value_i3, h_32, h_30⟩
            have _positive : ((Litex.denote _value_i3) = (M.number (0 : ℂ))) := _universal _value_i3 h_32
            have _negative : (¬ ((Litex.denote _value_i3) = (M.number (0 : ℂ)))) := h_30
            have _refute : ¬ (((Litex.denote _value_i3) = (M.number (0 : ℂ)))) := by
              simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
            exact _refute _positive)
            apply _not_universal
            intro _closing_i3 _closing_member_i3
            exact _universal _closing_i3 _closing_member_i3)
        )
      )
  )

theorem h_39 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_9 (M := M))
          exact _counterexample)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_counterexample_x5f_after_x5f_universal_x5f_use_x2f_statement_x2e_lit
