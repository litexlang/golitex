import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_counterexample_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) → (((Litex.denote _value_i1) = (M.number (1 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
                    have h_12 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0) := (by
                      let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)
                      exact (by
                        let _set := _atomic_wd_1_1
                        exact ((Litex.inInsert_iff (Litex.number (M := M) (0 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
                    have h_13 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_12
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    have h_14 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := rfl
                    have h_15 : ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))
                    exact ⟨_value_i2, h_12, h_15⟩
                )
            )
          exact (by
            classical
            intro _universal
            have _counterexample : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_18 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) := h_4
            rcases _counterexample with ⟨_value_i1, h_18, h_16⟩
            have _positive : ((Litex.denote _value_i1) = (M.number (1 : ℂ))) := _universal _value_i1 h_18
            have _negative : (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ)))) := h_16
            have _refute : ¬ (((Litex.denote _value_i1) = (M.number (1 : ℂ)))) := by
              simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
            exact _refute _positive)
        )
      )
  )

theorem h_23 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (¬ ((Litex.denote _value_i1) = (M.number (1 : ℂ))))) :=
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

noncomputable def _value_i5 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) from (h_23 (M := M))))

theorem h_34 : Litex.In (_value_i5 (M := M)) (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) from (h_23 (M := M)))))))
      )
  )

theorem h_35 : Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (_value_i5 (M := M))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_34 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_36 : ¬ Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) from (h_23 (M := M)))))))
      )
  )

theorem h_37 : ¬ Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_36 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_counterexample_x2f_statement_x2e_lit
