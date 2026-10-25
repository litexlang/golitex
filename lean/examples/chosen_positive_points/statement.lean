import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_positive_x5f_points_x2f_statement_x2e_lit

universe u v1 v2 v5 v6
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

theorem h_23 : Litex.IsNonempty (struct_1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          exact ⟨Litex.denote (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))), (by
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
              have h_20 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
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
                  simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_20))⟩
        )
      )
  )

theorem h_24 : (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact Litex.IsNonempty _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact (h_23 (M := M)))

variable {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M)))

theorem h_28 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1)
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

theorem h_30 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h30 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_28 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_31 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h29 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_32 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h30 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_33 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_34 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_35 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (((_struct_members_1 (M := M)) _value_i5).mp h_27).2
      )
  )

theorem h_36 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_27).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          exact (h_35 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_27))
      )
  )

include M in
private theorem _sketch_5 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_27 : Litex.In _value_i5 (struct_1 (M := M))) : True := by
  have h_43 : (by
    let _atomic_wd_1_0 := (struct_1 (M := M))
    exact Litex.IsNonempty _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (struct_1 (M := M))
    exact (h_23 (M := M)))

  obtain ⟨_witness_i6, _member_i6⟩ := h_43

  let _value_i6 := Litex.semanticObject (M := M) _witness_i6 (M.member_isSet _member_i6)

  have h_46 : Litex.In _value_i6 (struct_1 (M := M)) := _member_i6

  have h_47 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1)
        )
    )

  let _object_h48 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_47 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

  have h_48 : Litex.In _object_h48 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_47 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  let _object_h49 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_47 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

  have h_49 : Litex.In _object_h49 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_47 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_50 : Litex.Same (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h48 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_51 : Litex.Same (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h49 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_52 : Litex.In (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  have h_53 : Litex.In (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_54 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
    (by
      litex_checked_step =>
        exact (
          (((_struct_members_1 (M := M)) _value_i6).mp h_46).2
        )
    )
  have h_60 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          ((((_struct_members_1 (M := M)) _value_i6).mp (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_46)).1)
        )
    )

  let _object_h61 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_60 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

  have h_61 : Litex.In _object_h61 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_60 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  let _object_h62 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_60 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

  have h_62 : Litex.In _object_h62 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_60 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_63 : Litex.Same (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h61 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_64 : Litex.Same (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h62 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_65 : Litex.In (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i6).mp (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_46)).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  have h_66 : Litex.In (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i6).mp (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_46)).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_67 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
    (by
      litex_checked_step =>
        exact (
          (((_struct_members_1 (M := M)) _value_i6).mp (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_46)).2
        )
    )
  have h_41 : (by
    let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i6).mp h_46).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact h_54)
        )
    )
  have _have_type_checks_i7 : True :=
    ((show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_72 : Litex.In _value_i7 (struct_1 (M := M))), True from by
      intro _Host_i7 _rep_i7 _value_i7 h_72
      have h_73 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
        have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) :=
        (by
          litex_checked_step =>
            exact (
              ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1)
            )
        )
      let _object_h74 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_73 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
      have h_74 : Litex.In _object_h74 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_73 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      let _object_h75 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_73 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
      have h_75 : Litex.In _object_h75 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_73 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_76 : Litex.Same (Litex.cartCall _value_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h74 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_77 : Litex.Same (Litex.cartCall _value_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h75 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_78 : Litex.In (Litex.cartCall _value_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      have h_79 : Litex.In (Litex.cartCall _value_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i7).mp h_72).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_80 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i7) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
        (by
          litex_checked_step =>
            exact (
              (((_struct_members_1 (M := M)) _value_i7).mp h_72).2
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
      have h_220 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
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
          simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_220)))
  let _object_i7 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
  have h_301 : Litex.In _object_i7 (struct_1 (M := M)) :=
    (by
      litex_checked_step =>
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
              have h_220 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
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
                  simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_220))
        )
    )
  have h_310 : Litex.Same _object_i7 _object_i7 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))))
        )
    )
  have h_302 : Litex.In _object_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1)
        )
    )
  let _object_h303 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (1 : ℂ)) h_302 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_303 : Litex.In _object_h303 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_302 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h304 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (2 : ℂ)) h_302 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_304 : Litex.In _object_h304 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_302 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_305 : Litex.Same (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h303 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_306 : Litex.Same (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h304 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_307 : Litex.In (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  have h_308 : Litex.In (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_309 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _object_i7) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
    (by
      litex_checked_step =>
        exact (
          (((_struct_members_1 (M := M)) _object_i7).mp h_301).2
        )
    )
  have h_42 : (by
    let _atomic_wd_1_0 := (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.cartCall _object_i7 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _object_i7).mp h_301).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact h_309)
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_positive_x5f_points_x2f_statement_x2e_lit
