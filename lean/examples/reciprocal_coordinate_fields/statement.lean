import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit

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
  (Litex.DependentFields.cons (Litex.positiveReal (M := M)) (fun _raw_i1 => (Litex.DependentFields.cons (Litex.SetSemantics.insertValue (M.divValue (M.number (1 : ℂ)) _raw_i1) (Litex.SetSemantics.emptyValue (M := M))) (fun _raw_i2 => Litex.DependentFields.nil))))

theorem _struct_fields_wd_1 : Litex.DependentFields.WellFormed (_struct_fields_1 (M := M)) := by
  refine ⟨?_, ?_⟩
  · exact Litex.isSet (Litex.RPos (M := M))
  · intro _raw_i1 h_1
    let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i1 (M.member_isSet h_1)
    have h_2 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i1 h_1)
          )
      )
    have h_3 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_2)
          )
      )
    have h_4 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_2) _litex_zero.symm)
          )
      )
    refine ⟨?_, ?_⟩
    · exact Litex.isSet (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_1) h_4);
    (let _setElement_0 := _wd_1_0;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    · intro _raw_i2 h_28
      let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i2 (M.member_isSet h_28)
      have h_29 : Litex.Same _value_i2 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_1) h_4) :=
        (by
          litex_checked_step =>
            exact (
              (by
                have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_1) h_4)) (Litex.SetSemantics.emptyValue (M := M))) := h_28
                exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
            )
        )
      exact True.intro

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.DependentCartObj M 2) :=
  Litex.dependentCart (_struct_fields_1 (M := M)) (_struct_fields_wd_1 (M := M))

theorem h_32 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_45 : Litex.In _value_i5 (struct_1 (M := M))), (by
  have h_51 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.RPos (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  have h_52 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51)
        )
    )
  have h_54 : ¬ Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_52) _litex_zero.symm)
        )
    )
  exact (((by
    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((by
    let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51) h_54)
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_45
          have h_46 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.RPos (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45 (1 : Fin 2))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.RPos (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45 (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45)
                )
            )
          let _object_h47 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_46 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_47 : Litex.In _object_h47 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_46 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h48 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_46 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_48 : Litex.In _object_h48 (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45 (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_46 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_49 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h47 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_50 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h48 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_51 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_52 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51)
                )
            )
          have h_53 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_52)
                )
            )
          have h_54 : ¬ Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_52) _litex_zero.symm)
                )
            )
          have h_55 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45 (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_56 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51) h_54) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51) h_54)) (Litex.SetSemantics.emptyValue (M := M))) := h_55
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_30 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact h_54)
                )
            )
          have h_31 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.positiveRealToComplex (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 h_45) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_51) h_54)
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          exact (And.intro h_30 h_31)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit
