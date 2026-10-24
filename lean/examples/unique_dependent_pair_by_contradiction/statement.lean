import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_dependent_x5f_pair_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i2 (let _setElement_0 := _value_i1;
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Same _value_i2 _value_i1) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (Litex.SetSemantics.insertValue (Litex.denote _unique_left_i1) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (Litex.SetSemantics.insertValue (Litex.denote _unique_right_i1) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _unique_left_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _unique_right_i1))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)])) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_20 : ∀ (_value_i1 : Litex.Obj (M := M) M.Value) (h_21 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (_value_i2 : Litex.Obj (M := M) M.Value) (h_23 : Litex.In _value_i2 (let _setElement_0 := _value_i1;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) (h_1 : Litex.Same _value_i2 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i8 (let _setElement_0 := _value_i7;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (h_17 : Litex.Same _value_i8 _value_i7), ((¬ Litex.Same _value_i7 _value_i1) ∨ (¬ Litex.Same _value_i8 _value_i2)) := (by
            classical
            intro _value_i1 h_21 _value_i2 h_23 h_1
            have h_22 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_21
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_24 : Litex.Same _value_i2 _value_i1 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M))) := h_23
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)), h_21, (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)), h_23, h_1⟩
            · intro _unique_left_i1 _member_left_i1 _unique_left_i2 _member_left_i2 _unique_right_i1 _member_right_i1 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0
              have _same_left_i1 : Litex.denote _unique_left_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _unique_left_i2, _member_left_i2, _body_left_0, (Or.inl _different)⟩
              have _same_left_i2 : Litex.denote _unique_left_i2 = Litex.denote _value_i2 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _unique_left_i2, _member_left_i2, _body_left_0, (Or.inr _different)⟩
              have _same_right_i1 : Litex.denote _unique_right_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _unique_right_i2, _member_right_i2, _body_right_0, (Or.inl _different)⟩
              have _same_right_i2 : Litex.denote _unique_right_i2 = Litex.denote _value_i2 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _unique_right_i2, _member_right_i2, _body_right_0, (Or.inr _different)⟩
              simp only [_same_left_i1, _same_left_i2, _same_right_i1, _same_right_i2])
          rcases (show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_29 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_31 : Litex.In _value_i4 (let _setElement_0 := _value_i3;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ∃ (h_3 : Litex.Same _value_i4 _value_i3), ((¬ Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ))) ∨ (¬ Litex.Same _value_i4 (Litex.number (M := M) (7 : ℂ)))) from (by
            have h_46 : (by
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
            have h_49 : (by
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
            have h_52 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            rcases ((show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_23 : Litex.In _value_i2 (let _setElement_0 := _value_i1;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_1 : Litex.Same _value_i2 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i8 (let _setElement_0 := _value_i7;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)), ∃ (h_17 : Litex.Same _value_i8 _value_i7), ((¬ Litex.Same _value_i7 _value_i1) ∨ (¬ Litex.Same _value_i8 _value_i2)) from (fun {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_23 : Litex.In _value_i2 (let _setElement_0 := _value_i1;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) (h_1 : Litex.Same _value_i2 _value_i1) => by
              have h_22 : Litex.Same _value_i1 (Litex.number (M := M) (7 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_21
                        exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                    )
                )
              have h_24 : Litex.Same _value_i2 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M))) := h_23
                        exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                    )
                )
              exact h_20 (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_21 (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_23 h_1)) (Litex.number (M := M) (7 : ℂ)) h_46 (Litex.number (M := M) (7 : ℂ)) h_49 h_52) with ⟨_value_i3, h_29, _value_i4, h_31, h_3, h_6⟩
            have h_30 : Litex.Same _value_i3 (Litex.number (M := M) (7 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_29
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_32 : Litex.Same _value_i4 _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i4) (Litex.SetSemantics.insertValue (Litex.denote _value_i3) (Litex.SetSemantics.emptyValue (M := M))) := h_31
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
            have _exist_match_1 : Litex.Same (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) := (Litex.sameRefl (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            have _exist_match_2 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
            have _exist_match_3 : Litex.Same (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (7 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (7 : ℂ)))
            exact ⟨_value_i3, h_29, _value_i4, h_31, h_3, h_6⟩
          )) with ⟨_value_i5, h_54, _value_i6, h_56, h_58, h_61⟩

          have h_55 : Litex.Same _value_i5 (Litex.number (M := M) (7 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i5) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (7 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_54
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )

          have h_57 : Litex.Same _value_i6 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _value_i6) (Litex.SetSemantics.insertValue (Litex.denote _value_i5) (Litex.SetSemantics.emptyValue (M := M))) := h_56
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          exact (by
            have _asserted : ((¬ Litex.Same _value_i5 (Litex.number (M := M) (7 : ℂ))) ∨ (¬ Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ)))) := h_61
            have _denied : ¬ (((¬ Litex.Same _value_i5 (Litex.number (M := M) (7 : ℂ))) ∨ (¬ Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))))) := (by
            classical
            simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show (Litex.Same _value_i5 (Litex.number (M := M) (7 : ℂ))) ∧ (Litex.Same _value_i6 (Litex.number (M := M) (7 : ℂ))) from (And.intro h_55 ((h_57).trans h_55))))
            exact _denied _asserted)
        )
      )
  )

theorem h_264 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (Litex.SetSemantics.insertValue (Litex.denote _value_i9) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (Litex.SetSemantics.insertValue (Litex.denote _value_i10) (Litex.SetSemantics.emptyValue (M := M)))) (h_259 : ((Litex.denote _value_i11) = (Litex.denote _value_i9))) (h_260 : ((Litex.denote _value_i12) = (Litex.denote _value_i10))), ((((Litex.denote _value_i9) = (Litex.denote _value_i10))) ∧ (((Litex.denote _value_i11) = (Litex.denote _value_i12)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i11 _rep_i11 _value_i11 _membership_i11 _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i12 _rep_i12 _value_i12 _membership_i12 h_259 h_260
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (Litex.SetSemantics.insertValue (Litex.denote _unique_left_i1) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (Litex.SetSemantics.insertValue (M.number (7 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (Litex.SetSemantics.insertValue (Litex.denote _unique_right_i1) (Litex.SetSemantics.emptyValue (M := M)))) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _unique_left_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _unique_right_i1))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)]) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) _membership_i12 h_259 h_260
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_dependent_x5f_pair_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
