import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_replacement_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v8 v9 v10
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) : Prop :=
  ∃ (h_2 : Litex.IsSet _value_i1), ∃ (h_3 : Litex.IsSet _value_i2), Litex.Same _value_i2 _value_i1

theorem h_7 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_27 : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_31 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_32 : Litex.IsSet _value_i6) (h_4 : ((prop_1 (M := M)) _value_i4 _value_i5)) (h_5 : ((prop_1 (M := M)) _value_i4 _value_i6)), Litex.Same _value_i5 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_27 _Host_i5 _rep_i5 _value_i5 h_31 _Host_i6 _rep_i6 _value_i6 h_32 h_4 h_5
          have h_33 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i4 _value_i5) from h_4))
          have h_34 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i5) from h_4)))
          have h_35 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i5) from h_4)))
          have h_38 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i4 _value_i6) from h_5))
          have h_39 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i6) from h_5)))
          have h_40 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i6) from h_5)))
          have h_6 : Litex.Same _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  ((h_35).trans (h_40).symm)
                )
            )
          exact h_6
        )
      )
  )

noncomputable def _object_i7 :=
  Litex.replacement (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (fun _replacement_x _replacement_y => (∃ (_predicate_witness : (M.isSet _replacement_x)), (∃ (_predicate_witness : (M.isSet _replacement_y)), (_replacement_y = _replacement_x)))) (by
    intro _replacement_x hx _replacement_y _replacement_z hy hp hz hq
    exact ((h_7 (M := M)) (Litex.semanticObject _replacement_x (M.member_isSet hx)) hx (Litex.semanticObject _replacement_y hy) hy (Litex.semanticObject _replacement_z hz) hz hp hq)
  )

theorem h_43 : Litex.IsSet (_object_i7 (M := M)) := Litex.isSet (_object_i7 (M := M))

theorem h_44 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_ : Litex.In _value_i8 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_ : Litex.IsSet _value_i9) (h_45 : (∃ (_predicate_witness : (M.isSet (Litex.denote _value_i8))), (∃ (_predicate_witness : (M.isSet (Litex.denote _value_i9))), ((Litex.denote _value_i9) = (Litex.denote _value_i8))))), Litex.In _value_i9 (_object_i7 (M := M)) := by
  intro _ _ _value_i8 hx _ _ _value_i9 _ h_45
  exact Litex.replacementIntro (_object_i7 (M := M)) _value_i8 _value_i9 hx h_45

theorem h_47 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_ : Litex.In _value_i10 (_object_i7 (M := M))), ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (_ : Litex.In _value_i11 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_predicate_witness : (M.isSet (Litex.denote _value_i11))), (∃ (_predicate_witness : (M.isSet (Litex.denote _value_i10))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)))) := by
  intro _ _ _value_i10 hy
  exact Litex.replacementElim (_object_i7 (M := M)) _value_i10 hy

theorem h_50 : Litex.IsSet (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_43 (M := M))
      )
  )

theorem h_53 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Exists.intro (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_74 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_53 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_2)
      )
  )

theorem h_75 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_53 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_3)
      )
  )

theorem h_76 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_53 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_1)
      )
  )

theorem h_77 : Litex.In (Litex.number (M := M) (1 : ℂ)) (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_84 : (by
            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_2_1) :=
            (by
              let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_2 := Litex.emptySet (M := M);
                let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (by
                let _set := _atomic_wd_2_1
                exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
          have h_88 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
            (h_74 (M := M))
          have h_95 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ))) :=
            (h_53 (M := M))
          exact (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i7 (M := M)) (_object_i7 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.sameRefl (_object_i7 (M := M))) ((h_44 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_84 (Litex.number (M := M) (1 : ℂ)) h_88 h_95))
        )
      )
  )

theorem h_101 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_103 : Litex.In _value_i12 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ((prop_1 (M := M)) _value_i12 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_116 : Litex.In (Litex.number (M := M) (1 : ℂ)) (_object_i7 (M := M)) :=
            (h_77 (M := M))
          rcases ((h_47 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_116) with ⟨_value_i12, h_103, h_100⟩
          have h_108 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i12 (Litex.number (M := M) (1 : ℂ))) from h_100))
          have h_109 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i12 (Litex.number (M := M) (1 : ℂ))) from h_100)))
          have h_110 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i12 (Litex.number (M := M) (1 : ℂ))) from h_100)))
          have _exist_match_0 : Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) := (Litex.sameRefl (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          have _exist_match_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
          exact ⟨_value_i12, h_103, h_100⟩
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_replacement_x2f_statement_x2e_lit
