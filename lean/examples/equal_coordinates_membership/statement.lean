import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_coordinates_x5f_membership_x2f_statement_x2e_lit

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

theorem h_8 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_21 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (h_4 : (by
  let _object_h22 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_21 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  let _object_h23 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_21 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact (by
    let _equal_wd_1_0 := _object_h23
    let _equal_wd_1_1 := _object_h22
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
)), (by
  let _object_h22 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_21 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  let _object_h23 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_21 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _object_w7 := (let _wd_1_0 := _object_h22;
  (let _setElement_0 := _wd_1_0;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  let _object_w13 := (let _wd_1_0 := (Litex.R (M := M));
  let _wd_1_1 := _object_w7;
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )))
  let _object_w14 := (struct_1 (M := M))
  exact (((by
    let _atomic_wd_1_0 := _object_h23
    let _atomic_wd_1_1 := _object_w7
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((((by
    let _atomic_wd_1_1 := _object_w13
    exact Litex.In _value_i5 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_1 := _object_w14
    exact Litex.In _value_i5 _atomic_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_21 h_4
          let _object_h22 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_21 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_22 : Litex.In _object_h22 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_21 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h23 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_21 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_23 : Litex.In _object_h23 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_21 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_w7 := (let _wd_1_0 := _object_h22;
          (let _setElement_0 := _wd_1_0;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          have h_5 : (by
            let _atomic_wd_1_0 := _object_h23
            let _atomic_wd_1_1 := _object_w7
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_h23
                    let _atomic_wd_1_1 := _object_w7
                    exact (by
                      let _set := _atomic_wd_1_1
                      exact ((Litex.inInsert_iff _atomic_wd_1_0 _set.val.element _set.val.tail _set.wd).mpr (Or.inl h_4))))
                )
            )
          have h_48 : Litex.Same _object_h23 _object_h22 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote _object_h23) (Litex.SetSemantics.insertValue (Litex.denote _object_h22) (Litex.SetSemantics.emptyValue (M := M))) := h_5
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          let _object_w13 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := _object_w7;
          (let _productChild_0 := _wd_1_0;
          let _productChild_1 := _wd_1_1;
          Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
            have _finiteProof_0 := ((Litex.isSet _productChild_0))
            have _finiteProof_1 := ((Litex.isSet _productChild_1))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )))
          have h_6 : (by
            let _atomic_wd_1_1 := _object_w13
            exact Litex.In _value_i5 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w13
                    exact (by
                      let _membership_function := _value_i5
                      let _membership_target := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_87 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_87)
                        have h_87 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_87
                        have h_88 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_87).1
                              )
                          )
                        have h_89 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_87).2.1
                              )
                          )
                        have h_90 : Litex.Le _value_i6 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_87).2.2
                              )
                          )
                        have h_91 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_87)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (let _wd_1_0 := (Litex.R (M := M));
                    let _wd_1_1 := _object_w7;
                    (Litex.union _wd_1_0 _wd_1_1)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))
                      exact (by
                      let _source_cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      have _source_member : Litex.In _membership_function _source_cart := h_21
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _coordinates : ∀ i : Fin 2, M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index i)) (_cart.val.factors i) := (by
                      have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2))) (Litex.denote (Litex.R (M := M))) from by
                        have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) := (by
                        have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 2) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                        exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function)) _index)
                        rw [_coordinate]
                        exact (by
                        let _atomic_wd_2_0 := _object_h22
                        exact h_22)))
                      have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2))) (Litex.denote _object_w7) from by
                        have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (2 : ℂ))) := (by
                        have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 2) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                        exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function)) _index)
                        rw [_coordinate]
                        exact (by
                        let _atomic_wd_2_0 := _object_h23
                        let _atomic_wd_2_1 := _object_w7
                        exact h_5)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )
                      have _member : Litex.In _membership_function _cart := Litex.FiniteFunction.cart_of_coordinates _source_member _coordinates
                      have _carrier_same : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _membership_function _membership_function _cart _target (Litex.sameRefl _) _carrier_same.symm _member)))
                )
            )
          let _object_h116 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_6 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_116 : Litex.In _object_h116 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h117 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_6 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_117 : Litex.In _object_h117 _object_w7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_w14 := (struct_1 (M := M))
          have h_7 : (by
            let _atomic_wd_1_1 := _object_w14
            exact Litex.In _value_i5 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w14
                    exact ((Litex.inDependentCart_iff _value_i5 (struct_1 (M := M)) _struct_indices_1 _struct_indices_spec_1).mpr (by
                      let _atomic_wd_2_1 := _object_w13
                      exact h_6)))
                )
            )
          exact (And.intro h_5 (And.intro h_6 h_7))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_coordinates_x5f_membership_x2f_statement_x2e_lit
