import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_member_x5f_coordinate_x5f_pairs_x2f_statement_x2e_lit

universe u v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

def _struct_indices_1 : Fin 2 → ℂ :=
  ![1, 2]

theorem _struct_indices_spec_1 : ∀ i, _struct_indices_1 i = ((i.val + 1 : ℕ) : ℂ) := by
  intro i
  fin_cases i <;> norm_num [_struct_indices_1]

noncomputable def _struct_fields_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.DependentFields M 2 :=
  (Litex.DependentFields.cons (Litex.denote _value_i1) (fun _raw_i2 => (Litex.DependentFields.cons _raw_i2 (fun _raw_i3 => Litex.DependentFields.nil))))

theorem _struct_fields_wd_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.DependentFields.WellFormed ((_struct_fields_1 (M := M)) _value_i1 h_1) := by
  refine ⟨?_, ?_⟩
  · exact Litex.isSet _value_i1
  · intro _raw_i2 h_2
    let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i2 (M.member_isSet h_2)
    refine ⟨?_, ?_⟩
    · exact Litex.isSet _value_i2
    · intro _raw_i3 h_3
      let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i3 (M.member_isSet h_3)
      exact True.intro

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Obj (M := M) (Litex.DependentCartObj M 2) :=
  Litex.dependentCart ((_struct_fields_1 (M := M)) _value_i1 h_1) ((_struct_fields_wd_1 (M := M)) _value_i1 h_1)

noncomputable def _object_w1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

noncomputable def _object_w2 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(let _setElement_0 := _wd_1_0;
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0))

theorem h_4 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact (by
            let _set := _atomic_wd_1_1
            exact ((Litex.inInsert_iff _atomic_wd_1_0 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
      )
  )

theorem h_7 : Litex.Same (_object_w1 (M := M)) (_object_w1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (_object_w1 (M := M))) (Litex.SetSemantics.insertValue (Litex.denote (_object_w1 (M := M))) (Litex.SetSemantics.emptyValue (M := M))) := (h_4 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_8 : (by
  let _atomic_wd_1_1 := (_object_w1 (M := M))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w1 (M := M))
          exact (by
            let _set := _atomic_wd_1_1
            exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
      )
  )

theorem h_15 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_8 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

noncomputable def _object_w4 := (let _wd_1_0 := (_object_w1 (M := M));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(let _productChild_0 := _wd_1_0;
let _productChild_1 := _wd_1_1;
Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
  have _finiteProof_0 := ((Litex.isSet _productChild_0))
  have _finiteProof_1 := ((Litex.isSet _productChild_1))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)))

noncomputable def _object_w5 := (let _wd_1_0 := (_object_w2 (M := M));
((struct_1 (M := M)) _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  exact (Litex.isSet _atomic_wd_1_0))))

theorem h_16 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  let _atomic_wd_1_1 := (_object_w5 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w4 (M := M))
          let _atomic_wd_1_1 := (_object_w5 (M := M))
          exact (Litex.tupleInDependentCart _atomic_wd_1_0 ((struct_1 (M := M)) (_object_w2 (M := M)) (by
            let _atomic_wd_2_0 := (_object_w2 (M := M))
            exact (Litex.isSet _atomic_wd_2_0))) (by exact ⟨(by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            let _atomic_wd_2_1 := (_object_w2 (M := M))
            exact (h_4 (M := M))), ⟨(by
            let _atomic_wd_2_1 := (_object_w1 (M := M))
            exact (h_8 (M := M))), True.intro⟩⟩)))
      )
  )

theorem h_40 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_42 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_46 : Litex.In _value_i7 ((struct_1 (M := M)) _value_i6 h_42)), (((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 _value_i6)) ∧ ((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _atomic_wd_1_1 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_42 _Host_i7 _rep_i7 _value_i7 h_46
          have h_47 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote _value_i6, Litex.denote (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))] (by
            have _finiteProof_0 := (Litex.isSet _value_i6)
            have _finiteProof_1 := (Litex.isSet (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46)
                )
            )
          let _object_h48 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_47 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_48 : Litex.In _object_h48 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_47 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h49 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_47 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_49 : Litex.In _object_h49 (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_47 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_50 : Litex.Same (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h48 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_51 : Litex.Same (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h49 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_52 : Litex.In (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_53 : Litex.In (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_38 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact (Litex.inOfSame _object_h48 _atomic_wd_1_0 _value_i6 _value_i6 (h_50).symm (show @Eq M.Value _ _ from Eq.refl _) h_48))
                )
            )
          have h_39 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _atomic_wd_1_1 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    let _atomic_wd_1_1 := (Litex.cartCall _value_i7 (Litex.dependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i7 ((struct_1 (M := M)) _value_i6 h_42) _struct_indices_1 _struct_indices_spec_1 h_46) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact (Litex.inOfSame _object_h49 _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_1 (h_51).symm (show @Eq M.Value _ _ from Eq.refl _) h_49))
                )
            )
          exact (And.intro h_38 h_39)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_member_x5f_coordinate_x5f_pairs_x2f_statement_x2e_lit
