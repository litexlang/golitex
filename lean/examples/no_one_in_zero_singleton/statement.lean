import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_no_x5f_one_x5f_in_x5f_zero_x5f_singleton_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4
          have h_5 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          change (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ))))
          exact (Or.elim ((Litex.SetSemantics.insert_members (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i1)).mp h_4) (fun _enumerated_case => (by
            have h_6 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) :=
              (by
                litex_checked_step =>
                  exact (
                    h_4
                  )
              )
            have h_7 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_6
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_8 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    _enumerated_case
                  )
              )
            have h_3 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.notSameOfSame (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_7).symm (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))
                  )
              )
            have h_23 : ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) h_7 (show @Eq M.Value _ _ from Eq.refl _) h_3)
                  )
              )
            show (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ))))
            exact Eq.mpr (congrArg (fun (_enumeration_value : M.Value) => (¬ (_enumeration_value = (M.number (1 : ℂ))))) _enumerated_case) (show (¬ ((M.number (0 : ℂ)) = (M.number (1 : ℂ)))) from h_23)
          )) (fun _enumerated_tail => (False.elim (Litex.SetSemantics.empty_members (Litex.denote _value_i1) _enumerated_tail))))
        )
      )
  )

theorem h_31 : ¬ (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_36 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_38 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_39 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) := (by
            classical
            simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
          rcases (show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_41 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) from h_38) with ⟨_value_i4, h_44, h_46⟩

          have h_45 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i4) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_44
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_34 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_62 : (by
                      let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact Litex.In _value_i4 _atomic_wd_2_1) :=
                      (by
                        let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                          let _setTail_1 := Litex.emptySet (M := M);
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact h_44)
                    exact (Litex.notSameOfSame _value_i4 _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((h_2 (M := M)) _value_i4 h_62))
                  )
                )
            )
          exact (by
            have _asserted : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) := h_46
            have _denied : ¬ (Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ))) := h_34
            exact _denied _asserted)
        )
      )
  )

theorem h_77 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i5) = (M.number (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i5 _rep_i5 _value_i5 _membership_i5
          have _excluded : ¬ ((∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), ((Litex.denote _value_i2) = (M.number (1 : ℂ))))) := (h_31 (M := M))
          have _no_body : ¬ (((Litex.denote _value_i5) = (M.number (1 : ℂ)))) := by
            intro _candidate
            have h_30 := _candidate
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5), _membership_i5, h_30⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )

theorem h_79 : ¬ (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_31 (M := M))
      )
  )

theorem h_84 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i7) = (M.number (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i7 _rep_i7 _value_i7 _membership_i7
          have _excluded : ¬ ((∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i6) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), ((Litex.denote _value_i6) = (M.number (1 : ℂ))))) := (h_79 (M := M))
          have _no_body : ¬ (((Litex.denote _value_i7) = (M.number (1 : ℂ)))) := by
            intro _candidate
            have h_78 := _candidate
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7), _membership_i7, h_78⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_no_x5f_one_x5f_in_x5f_zero_x5f_singleton_x2f_statement_x2e_lit
