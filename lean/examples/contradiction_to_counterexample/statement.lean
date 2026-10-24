import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_to_x5f_counterexample_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) → (((Litex.denote _value_i1) = (M.number (1 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_6 : ∀ (_value_i1 : Litex.Obj (M := M) M.Value) (h_7 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) := (Classical.byContradiction _litex_negated_goal)
          exact (by
            have _asserted : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (by
            have h_22 : (by
              let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact Litex.In (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
              (by
                let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (by
                  let _set := _atomic_wd_1_1
                  exact ((Litex.inInsert_iff (Litex.number (M := M) (0 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
            exact (Eq.trans (Eq.symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))) (Eq.trans ((show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) from (fun {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)) => by
            have h_8 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_7
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            exact h_6 (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_7)) (Litex.number (M := M) (0 : ℂ)) h_22) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))
          )
            have _denied : ¬ (Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ))) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))
            exact _denied _asserted)
        )
      )
  )

theorem h_29 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ))))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_2 (M := M))
          exact _counterexample)
      )
  )

noncomputable def _value_i3 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) from (h_29 (M := M))))

theorem h_34 : Litex.In (_value_i3 (M := M)) (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) from (h_29 (M := M)))))))
      )
  )

theorem h_35 : Litex.Same (_value_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (_value_i3 (M := M))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_34 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_36 : ¬ Litex.Same (_value_i3 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) from (h_29 (M := M)))))))
      )
  )

theorem h_37 : ¬ Litex.Same (_value_i3 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_36 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_to_x5f_counterexample_x2f_statement_x2e_lit
