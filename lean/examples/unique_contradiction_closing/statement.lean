import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit

universe u v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_3 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.isSet (Litex.number (M := M) (7 : ℂ)))
          have h_8 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) := (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_1
              exact ((Litex.inInsert_iff (Litex.number (M := M) (7 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
          have h_9 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_8
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_10 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) := rfl
          have h_11 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨⟨_value_i1, h_8, h_11⟩, (by
            intro _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0
            exact (show ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_41 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_43 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (h_13 : Litex.Same _value_i2 (Litex.number (M := M) (7 : ℂ))) (h_14 : Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ))), Litex.Same _value_i2 _value_i3 from (by
            intro _Host_i2 _rep_i2 _value_i2 h_41 _Host_i3 _rep_i3 _value_i3 h_43 h_13 h_14
            have h_42 : Litex.Same _value_i2 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_41
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_44 : Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_43
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_15 : Litex.Same _value_i2 _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    ((h_42).trans (h_44).symm)
                  )
              )
            exact h_15
          )) _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0)⟩
      )
  )

theorem h_49 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_membership_i4 : M.mem (Litex.denote _value_i4) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (h_46 : ((Litex.denote _value_i4) = (M.number (7 : ℂ)))) (h_47 : ((Litex.denote _value_i5) = (M.number (7 : ℂ)))), ((Litex.denote _value_i4) = (Litex.denote _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 _membership_i4 _Host_i5 _rep_i5 _value_i5 _membership_i5 h_46 h_47
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i4) (Litex.isSet _value_i4)) _membership_i4 (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) _membership_i5 h_46 h_47
          exact _same)
      )
  )

theorem h_51 : (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_54 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))) ∧ (∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i6) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i6) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_59 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_60 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (h_50 : Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_62 : Litex.In _value_i8 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (h_57 : Litex.Same _value_i8 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i8 _value_i6 := (by
            classical
            intro _value_i6 h_60 h_50
            have h_61 : Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i6) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_60
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)), h_60, h_50⟩
            · intro _unique_left_i6 _member_left_i6 _unique_right_i6 _member_right_i6 _body_left_0 _body_right_0
              have _same_left_i6 : Litex.denote _unique_left_i6 = Litex.denote _value_i6 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i6, _member_left_i6, _body_left_0, _different⟩
              have _same_right_i6 : Litex.denote _unique_right_i6 = Litex.denote _value_i6 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i6, _member_right_i6, _body_right_0, _different⟩
              simp only [_same_left_i6, _same_right_i6])
          exact (by
            have _unique_exists : (∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_64 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), Litex.Same _value_i7 (Litex.number (M := M) (7 : ℂ))) ∧ (∀ (_unique_left_i7 : Litex.Obj (M := M) M.Value) (_member_left_i7 : M.mem (Litex.denote _unique_left_i7) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i7 : Litex.Obj (M := M) M.Value) (_member_right_i7 : M.mem (Litex.denote _unique_right_i7) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i7) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i7) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i7) = (Litex.denote _unique_right_i7)) := (h_2 (M := M))
            have _alternative : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_74 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_52 : Litex.Same _value_i7 (Litex.number (M := M) (7 : ℂ))), ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i9 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), ∃ (h_67 : Litex.Same _value_i9 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i9 _value_i7 := (by
              intro _Host_i7 _rep_i7 _value_i7 h_74 h_52
              have h_75 : Litex.Same _value_i7 (Litex.number (M := M) (7 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        have _member : M.mem (Litex.denote _value_i7) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_74
                        exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                    )
                )
              exact ((show ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_60 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_50 : Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_62 : Litex.In _value_i8 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), ∃ (h_57 : Litex.Same _value_i8 (Litex.number (M := M) (7 : ℂ))), ¬ Litex.Same _value_i8 _value_i6 from (fun {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_60 : Litex.In _value_i6 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_50 : Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))) => by
              have h_61 : Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        have _member : M.mem (Litex.denote _value_i6) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_60
                        exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                    )
                )
              exact h_59 (Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)) h_60 h_50)) _value_i7 h_74 h_52)
            )
            rcases _unique_exists with ⟨_exists, _unique⟩
            rcases _exists with ⟨_unique_left_i7, _member_left_i7, _body_left_0⟩
            obtain ⟨_unique_right_i7, _member_right_i7, _body_right_0, _different⟩ := _alternative _unique_left_i7 _member_left_i7 _body_left_0
            have _same := _unique _unique_left_i7 _member_left_i7 _unique_right_i7 _member_right_i7 _body_left_0 _body_right_0
            exact _different _same.symm)
        )
      )
  )

theorem h_83 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (h_80 : ((Litex.denote _value_i10) = (M.number (7 : ℂ)))) (h_81 : ((Litex.denote _value_i11) = (M.number (7 : ℂ)))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11 h_80 h_81
          have _unique : ∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i6) = (M.number (7 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i6) = (M.number (7 : ℂ)))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6) := ((h_51 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 h_80 h_81
          exact _same)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit
