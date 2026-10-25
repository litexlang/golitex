import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_point_x5f_release_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))), True := by
  intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3
  have _struct_conditions_wd : ∀ (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), True := by
    intro h_1
    exact True.intro
  exact True.intro

noncomputable def _struct_base_1 : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _struct_condition_1 (_struct_raw : M.Value) : Prop :=
  (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) (Litex.CartObj M 2)) :=
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

theorem h_15 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_16 : Litex.In _value_i4 (struct_1 (M := M))), Litex.In _value_i4 (struct_1 (M := M)) → (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_16 _
          exact (((_struct_members_1 (M := M)) _value_i4).mp h_16).2)
      )
  )

include M in
theorem _have_type_checks_i5 : True :=
  ((show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_17 : Litex.In _value_i5 (struct_1 (M := M))), True from by
    intro _Host_i5 _rep_i5 _value_i5 h_17
    have h_18 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
      have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) :=
      (by
        litex_checked_step =>
          exact (
            ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1)
          )
      )
    let _object_h19 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_19 : Litex.In _object_h19 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h20 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_20 : Litex.In _object_h20 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_21 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h19 :=
      (by
        litex_checked_step =>
          exact (
            (by rfl)
          )
      )
    have h_22 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h20 :=
      (by
        litex_checked_step =>
          exact (
            (by rfl)
          )
      )
    have h_23 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    have h_24 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_17).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_25 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
      (by
        litex_checked_step =>
          exact (
            (((_struct_members_1 (M := M)) _value_i5).mp h_17).2
          )
      )
    exact True.intro
  ) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))) (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
  let _atomic_wd_1_1 := (struct_1 (M := M))
  exact (by
    have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
      calc
        _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
        _ = _ := by rfl
    have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (3 : ℂ)) := by
      calc
        _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
        _ = _ := by rfl
    have h_29 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
    refine ((_struct_members_1 (M := M)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 (_struct_base_1 (M := M)) (by
    have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
    have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )), ?_⟩
    change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)
    set_option linter.unusedSimpArgs false in
      set_option linter.unnecessarySimpa false in
        simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_29)))
noncomputable def _object_i5 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
theorem h_32 : Litex.In (_object_i5 (M := M)) (struct_1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact (by
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (3 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_29 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
            refine ((_struct_members_1 (M := M)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 (_struct_base_1 (M := M)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_29))
      )
  )
theorem h_41 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))))
      )
  )
theorem h_33 : Litex.In (_object_i5 (M := M)) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1)
      )
  )
noncomputable def _object_h34 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (1 : ℂ)) (h_33 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
theorem h_34 : Litex.In (_object_h34 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_33 (M := M)) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )
noncomputable def _object_h35 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (2 : ℂ)) (h_33 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
theorem h_35 : Litex.In (_object_h35 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_33 (M := M)) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )
theorem h_36 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h34 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )
theorem h_37 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h35 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )
theorem h_38 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )
theorem h_39 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )
theorem h_40 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).2
      )
  )

theorem h_47 : Litex.In (_object_i5 (M := M)) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact (h_32 (M := M)))).1)
      )
  )

noncomputable def _object_h48 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (1 : ℂ)) (h_47 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_48 : Litex.In (_object_h48 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_47 (M := M)) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h49 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (2 : ℂ)) (h_47 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_49 : Litex.In (_object_h49 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_47 (M := M)) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_50 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h48 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_51 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h49 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_52 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact (h_32 (M := M)))).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_53 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact (h_32 (M := M)))).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_54 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact (h_32 (M := M)))).2
      )
  )

theorem h_55 : (by
  let _atomic_wd_1_0 := (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          exact (h_40 (M := M)))
      )
  )

theorem h_60 : (by
  let _equal_wd_1_0 := (Litex.cartCall (_object_i5 (M := M)) (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) (_object_i5 (M := M))).mp (h_32 (M := M))).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_36 (M := M)) (Eq.trans (by
          let _tuple := (_object_i5 (M := M))
          have _receiver_eq : Litex.Same (_object_i5 (M := M)) _tuple := (h_41 (M := M))
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
          have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        ) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_point_x5f_release_x2f_statement_x2e_lit
