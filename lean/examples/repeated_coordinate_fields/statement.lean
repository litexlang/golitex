import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_repeated_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit

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

noncomputable def _object_w5 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w6 := (struct_1 (M := M))

theorem h_8 : (by
  let _atomic_wd_1_0 := (_object_w5 (M := M))
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w5 (M := M))
          let _atomic_wd_1_1 := (_object_w6 (M := M))
          exact (Litex.tupleInDependentCart _atomic_wd_1_0 (struct_1 (M := M)) (by exact ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ⟨(by
            let _atomic_wd_2_1 := (_object_w4 (M := M))
            exact (h_4 (M := M))), True.intro⟩⟩)))
      )
  )

theorem h_25 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_38 : Litex.In _value_i5 (_object_w6 (M := M))), (((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _atomic_wd_1_1 := (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
  let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _equal_wd_1_1 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_38
          have h_39 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38)
                )
            )
          let _object_h40 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_39 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_40 : Litex.In _object_h40 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_39 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h41 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_39 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_41 : Litex.In _object_h41 (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_39 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_42 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h40 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_43 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h41 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_44 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_45 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_46 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := h_45
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_23 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _atomic_wd_1_1 := (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2))
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    let _atomic_wd_1_1 := (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38 (1 : Fin 2))
                    exact (Litex.inOfSame _object_h41 _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_1 (h_43).symm (show @Eq M.Value _ _ from Eq.refl _) h_41))
                )
            )
          have h_59 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := h_23
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_24 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _equal_wd_1_1 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_38) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_46
                )
            )
          exact (And.intro h_23 h_24)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_repeated_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit
