import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_singleton_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_12 : ∀ (_value_i1 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (h_10 : Litex.Same _value_i4 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i4 _value_i1 := (by
            classical
            intro _value_i1 h_13 h_1
            have h_14 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_13
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)), h_13, h_1⟩
            · intro _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0
              have _same_left_i1 : Litex.denote _unique_left_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _body_left_0, _different⟩
              have _same_right_i1 : Litex.denote _unique_right_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _body_right_0, _different⟩
              simp only [_same_left_i1, _same_right_i1])
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_17 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (h_3 : Litex.Same _value_i2 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i2 (Litex.number (M := M) (7 : ℂ)) from (by
            have h_28 : (by
              let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact Litex.In (Litex.number (M := M) (7 : ℂ)) _atomic_wd_1_1) :=
              (by
                let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (by
                  let _set := _atomic_wd_1_1
                  exact ((Litex.inInsert_iff (Litex.number (M := M) (7 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
            have h_31 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            rcases ((show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_13 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), ∃ (h_10 : Litex.Same _value_i4 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i4 _value_i1 from (fun {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_13 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ))) => by
              have h_14 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_13
                        exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                    )
                )
              exact h_12 (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_13 h_1)) (Litex.number (M := M) (7 : ℂ)) h_28 h_31) with ⟨_value_i2, h_17, h_3, h_4⟩
            have h_18 : Litex.Same _value_i2 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_17
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have _exist_match_0 : Litex.Same (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) := (Litex.sameRefl (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            have _exist_match_1 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
            have _exist_match_2 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
            exact ⟨_value_i2, h_17, h_3, h_4⟩
          )) with ⟨_value_i3, h_33, h_35, h_36⟩

          have h_34 : Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_33
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          exact (by
            have _asserted : Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ)) := h_34
            have _denied : ¬ (Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ))) := h_36
            exact _denied _asserted)
        )
      )
  )

theorem h_48 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_membership_i6 : M.mem (Litex.denote _value_i6) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (h_45 : ((Litex.denote _value_i5) = (M.number (7 : ℂ)))) (h_46 : ((Litex.denote _value_i6) = (M.number (7 : ℂ)))), ((Litex.denote _value_i5) = (Litex.denote _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 _membership_i5 _Host_i6 _rep_i6 _value_i6 _membership_i6 h_45 h_46
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) _membership_i5 (Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)) _membership_i6 h_45 h_46
          exact _same)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_singleton_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
