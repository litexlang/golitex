import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_repeated_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

def _struct_indices_1 : Fin 2 → ℂ :=
  ![1, 2]

theorem _struct_indices_spec_1 : ∀ i, _struct_indices_1 i = ((i.val + 1 : ℕ) : ℂ) := by
  intro i
  fin_cases i <;> norm_num [_struct_indices_1]

noncomputable def _struct_fields_1 : Litex.DependentFields M 2 :=
  (Litex.DependentFields.cons (M.standard Litex.StandardSetValue.real) (fun _raw_i1 => (Litex.DependentFields.cons (Litex.SetSemantics.insertValue _raw_i1 (Litex.SetSemantics.emptyValue (M := M))) (fun _raw_i2 => Litex.DependentFields.nil))))

theorem _struct_fields_wd_1 : Litex.DependentFields.WellFormed (_struct_fields_1 (M := M)) := by
  refine ⟨?_, ?_⟩
  · exact Litex.isSet (Litex.R (M := M))
  · intro _raw_i1 h_1
    let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i1 (M.member_isSet h_1)
    refine ⟨?_, ?_⟩
    · exact Litex.isSet (let _setElement_0 := _value_i1;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    · intro _raw_i2 h_2
      let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i2 (M.member_isSet h_2)
      have h_3 : Litex.Same _value_i2 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (by
                have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M))) := h_2
                exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
            )
        )
      exact True.intro

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.DependentCartObj M 2) :=
  Litex.dependentCart (_struct_fields_1 (M := M)) (_struct_fields_wd_1 (M := M))

noncomputable def _object_w4 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

theorem h_4 : (by
  let _atomic_wd_1_1 := (_object_w4 (M := M))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w4 (M := M))
          exact (by
            let _set := _atomic_wd_1_1
            exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
      )
  )

theorem h_7 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_4 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_23 : Litex.IsNonempty (struct_1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          exact ⟨Litex.denote (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))), (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact (Litex.tupleInDependentCart _atomic_wd_1_0 (struct_1 (M := M)) (by exact ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ⟨(by
              let _atomic_wd_2_1 := (_object_w4 (M := M))
              exact (h_4 (M := M))), True.intro⟩⟩)))⟩
        )
      )
  )

theorem h_24 : (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact Litex.IsNonempty _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact (h_23 (M := M)))

variable {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M)))

theorem h_28 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27)
      )
  )

noncomputable def _object_h29 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) (h_28 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_29 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h29 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_28 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h30 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) (h_28 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_30 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h30 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_28 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_31 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h29 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_32 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h30 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_33 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_34 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_35 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := (h_34 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27)
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_43 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_27))
      )
  )

noncomputable def _object_h44 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) (h_43 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_44 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h44 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_43 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h45 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) (h_43 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_45 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h45 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_43 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_46 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h44 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_47 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h45 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_48 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_27)) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_49 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27 (1 : Fin 2)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_27)) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_50 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := (h_49 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27)
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_51 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : (by
  let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _equal_wd_1_1 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_27) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_35 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27)
      )
  )

include M in
private theorem _sketch_7 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : True := by
  have _have_type_checks_i6 : True :=
    ((show ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_54 : Litex.In _value_i6 (struct_1 (M := M))), True from by
      intro _Host_i6 _rep_i6 _value_i6 h_54
      have h_55 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54 (1 : Fin 2))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
        have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54 (1 : Fin 2)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54)
            )
        )
      let _object_h56 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_55 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
      have h_56 : Litex.In _object_h56 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_55 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      let _object_h57 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_55 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
      have h_57 : Litex.In _object_h57 (Litex.dependentFieldCarrier _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54 (1 : Fin 2)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_55 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_58 : Litex.Same (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h56 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_59 : Litex.Same (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h57 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_60 : Litex.In (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      have h_61 : Litex.In (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54 (1 : Fin 2)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_62 : Litex.Same (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
        (by
          litex_checked_step =>
            exact (
              (by
                have _member : M.mem (Litex.denote (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i6 (Litex.dependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_54) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := h_61
                exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
            )
        )
      exact True.intro
    ) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (by
    let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
    let _atomic_wd_1_1 := (struct_1 (M := M))
    exact (Litex.tupleInDependentCart _atomic_wd_1_0 (struct_1 (M := M)) (by exact ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ⟨(by
      let _atomic_wd_2_1 := (_object_w4 (M := M))
      exact (h_4 (M := M))), True.intro⟩⟩))))
  let _object_i6 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
  have h_144 : Litex.In _object_i6 (struct_1 (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact (Litex.tupleInDependentCart _atomic_wd_1_0 (struct_1 (M := M)) (by exact ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ⟨(by
              let _atomic_wd_2_1 := (_object_w4 (M := M))
              exact (h_4 (M := M))), True.intro⟩⟩)))
        )
    )
  have h_153 : Litex.Same _object_i6 _object_i6 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))))
        )
    )
  have h_145 : Litex.In _object_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144 (1 : Fin 2))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144 (1 : Fin 2)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144)
        )
    )
  let _object_h146 := (Litex.cartCall _object_i6 _ (Litex.number (M := M) (1 : ℂ)) h_145 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_146 : Litex.In _object_h146 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_145 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h147 := (Litex.cartCall _object_i6 _ (Litex.number (M := M) (2 : ℂ)) h_145 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_147 : Litex.In _object_h147 (Litex.dependentFieldCarrier _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144 (1 : Fin 2)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_145 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_148 : Litex.Same (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h146 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_149 : Litex.Same (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h147 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_150 : Litex.In (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  have h_151 : Litex.In (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144 (1 : Fin 2)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_152 : Litex.Same (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            have _member : M.mem (Litex.denote (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := h_151
            exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
        )
    )
  have h_53 : (by
    let _equal_wd_1_0 := (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    let _equal_wd_1_1 := (Litex.cartCall _object_i6 (Litex.dependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _object_i6 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_144) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          h_152
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_repeated_x5f_coordinates_x2f_statement_x2e_lit
