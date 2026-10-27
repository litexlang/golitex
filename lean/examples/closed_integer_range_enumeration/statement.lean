import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)))

noncomputable def _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0)

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((by
          let _range := _equal_wd_1_0
          let _list := _equal_wd_1_1
          change Litex.denote _range = Litex.denote _list
          have hr : Litex.denote _range = Litex.closedRangeValue (M.number ((1 : ℤ) : ℂ)) (M.number ((0 : ℤ) : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)).trans (congrArg M.number (by norm_num)))
          have hs : Litex.denote _list = (Litex.SetSemantics.emptyValue (M := M)) := Eq.refl _
          apply Litex.SetSemantics.ext _ _ (Litex.isSet _range) (Litex.isSet _list)
          intro x
          rw [hr, hs, Litex.closedRangeValue_members]
          simp only [Litex.SetSemantics.empty_members]
          constructor
          · rintro ⟨k, _, hlo, hhi⟩
            omega
          · exact False.elim
        ) : Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
      )
  )

noncomputable def _object_w3 := (Litex.closedRange (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))

noncomputable def _object_w4 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (0 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (0 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

theorem h_17 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((by
          let _range := _equal_wd_1_0
          let _list := _equal_wd_1_1
          change Litex.denote _range = Litex.denote _list
          have hr : Litex.denote _range = Litex.closedRangeValue (M.number ((0 : ℤ) : ℂ)) (M.number ((2 : ℤ) : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num)))
          have hs : Litex.denote _list = (Litex.SetSemantics.insertValue (M.number ((0 : ℤ) : ℂ)) (Litex.SetSemantics.insertValue (M.number ((1 : ℤ) : ℂ)) (Litex.SetSemantics.insertValue (M.number ((2 : ℤ) : ℂ)) (Litex.SetSemantics.emptyValue (M := M))))) := congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)).trans (congrArg M.number (by norm_num))) (congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) (congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) (Eq.refl _)))
          apply Litex.SetSemantics.ext _ _ (Litex.isSet _range) (Litex.isSet _list)
          intro x
          rw [hr, hs, Litex.closedRangeValue_members]
          simp only [Litex.SetSemantics.insert_members, Litex.SetSemantics.empty_members, or_false]
          constructor
          · rintro ⟨k, rfl, hlo, hhi⟩
            have h : k = (0 : ℤ) ∨ k = (1 : ℤ) ∨ k = (2 : ℤ) := by omega
            rcases h with h_0 | h_1 | h_2
            · subst k
              exact Or.inl (rfl)
            · subst k
              exact Or.inr (Or.inl (rfl))
            · subst k
              exact Or.inr (Or.inr (rfl))
          · intro h
            rcases h with h_0 | h_1 | h_2
            · exact ⟨(0 : ℤ), h_0, by omega, by omega⟩
            · exact ⟨(1 : ℤ), h_1, by omega, by omega⟩
            · exact ⟨(2 : ℤ), h_2, by omega, by omega⟩

        ) : Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
      )
  )

noncomputable def _object_w5 := (let _setElement_0 := (Litex.number (M := M) (4 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (5 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (4 : ℂ) (5 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

noncomputable def _object_w6 := (Litex.closedRange (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)))

theorem h_27 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((by
          let _range := _equal_wd_1_1
          let _list := _equal_wd_1_0
          change Litex.denote _range = Litex.denote _list
          have hr : Litex.denote _range = Litex.closedRangeValue (M.number ((4 : ℤ) : ℂ)) (M.number ((5 : ℤ) : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)).trans (congrArg M.number (by norm_num)))
          have hs : Litex.denote _list = (Litex.SetSemantics.insertValue (M.number ((4 : ℤ) : ℂ)) (Litex.SetSemantics.insertValue (M.number ((5 : ℤ) : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) := congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) (congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)).trans (congrArg M.number (by norm_num))) (Eq.refl _))
          apply Litex.SetSemantics.ext _ _ (Litex.isSet _range) (Litex.isSet _list)
          intro x
          rw [hr, hs, Litex.closedRangeValue_members]
          simp only [Litex.SetSemantics.insert_members, Litex.SetSemantics.empty_members, or_false]
          constructor
          · rintro ⟨k, rfl, hlo, hhi⟩
            have h : k = (4 : ℤ) ∨ k = (5 : ℤ) := by omega
            rcases h with h_0 | h_1
            · subst k
              exact Or.inl (rfl)
            · subst k
              exact Or.inr (rfl)
          · intro h
            rcases h with h_0 | h_1
            · exact ⟨(4 : ℤ), h_0, by omega, by omega⟩
            · exact ⟨(5 : ℤ), h_1, by omega, by omega⟩

        ) : Litex.Same _equal_wd_1_1 _equal_wd_1_0).symm))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_integer_x5f_range_x5f_enumeration_x2f_statement_x2e_lit
