import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_repeated_x5f_coordinates_x2f_statement_x2e_lit

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
  · intro _raw_i1 h_2
    let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i1 (M.member_isSet h_2)
    refine ⟨?_, ?_⟩
    · exact Litex.isSet (let _setElement_0 := _value_i1;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    · intro _raw_i2 h_3
      let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject _raw_i2 (M.member_isSet h_3)
      have h_4 : Litex.Same _value_i2 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (by
                have _member : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (Litex.denote _value_i1) (Litex.SetSemantics.emptyValue (M := M))) := h_3
                exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
            )
        )
      have _struct_conditions_wd : ∀ (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), True := by
        intro h_1
        exact True.intro
      exact True.intro

noncomputable def _struct_base_1 : Litex.Obj (M := M) (Litex.DependentCartObj M 2) :=
  Litex.dependentCart (_struct_fields_1 (M := M)) (_struct_fields_wd_1 (M := M))

noncomputable def _struct_condition_1 (_struct_raw : M.Value) : Prop :=
  (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) (Litex.DependentCartObj M 2)) :=
  Litex.setBuilder (_struct_base_1 (M := M)) (fun _struct_value _ => (_struct_condition_1 (M := M)) (Litex.denote _struct_value))

theorem _struct_members_1 {_Host : Type _} [_rep : Litex.Representation M _Host] (_struct_value : Litex.Obj (M := M) _Host) :
    Litex.In _struct_value (struct_1 (M := M)) ↔ Litex.In _struct_value (_struct_base_1 (M := M)) ∧ (_struct_condition_1 (M := M)) (Litex.denote _struct_value) := by
  change Litex.In _struct_value (Litex.setBuilder (_struct_base_1 (M := M)) _) ↔ _
  rw [Litex.inSetBuilder_iff]
  constructor
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩

theorem h_16 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_17 : Litex.In _value_i4 (struct_1 (M := M))), Litex.In _value_i4 (struct_1 (M := M)) → (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_17 _
          exact (((_struct_members_1 (M := M)) _value_i4).mp h_17).2)
      )
  )

noncomputable def _object_w4 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

theorem h_18 : (by
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

theorem h_21 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_18 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

noncomputable def _object_w5 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w6 := (struct_1 (M := M))

theorem h_22 : (by
  let _atomic_wd_1_0 := (_object_w5 (M := M))
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w5 (M := M))
          let _atomic_wd_1_1 := (_object_w6 (M := M))
          exact (by
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_37 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
            refine ((_struct_members_1 (M := M)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInDependentCart _atomic_wd_1_0 (_struct_base_1 (M := M)) (by exact ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ⟨(by
            let _atomic_wd_2_1 := (_object_w4 (M := M))
            exact (h_18 (M := M))), True.intro⟩⟩)), ?_⟩
            change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_37))
      )
  )

theorem h_48 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_61 : Litex.In _value_i5 (_object_w6 (M := M))), (((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)) ∧ ((by
  let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  let _equal_wd_1_1 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_61
          have h_62 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.dependentFieldCarrier _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1) (1 : Fin 2))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.dependentFieldCarrier _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1) (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1))
                )
            )
          let _object_h63 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_62 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_63 : Litex.In _object_h63 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_62 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h64 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_62 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_64 : Litex.In _object_h64 (Litex.dependentFieldCarrier _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1) (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_62 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_65 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h63 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_66 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h64 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_67 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_68 : Litex.In (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.dependentFieldCarrier _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1) (1 : Fin 2)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_69 : Litex.Same (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))) (Litex.SetSemantics.emptyValue (M := M))) := h_68
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_70 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (((_struct_members_1 (M := M)) _value_i5).mp h_61).2
                )
            )
          have h_46 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact h_70)
                )
            )
          have h_47 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (2 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _equal_wd_1_1 := (Litex.cartCall _value_i5 (Litex.dependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (Litex.number (M := M) (1 : ℂ)) (Litex.inDependentCartAt _value_i5 (_struct_base_1 (M := M)) _struct_indices_1 _struct_indices_spec_1 ((((_struct_members_1 (M := M)) _value_i5).mp h_61).1)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_69
                )
            )
          exact (And.intro h_46 h_47)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_repeated_x5f_coordinates_x2f_statement_x2e_lit
