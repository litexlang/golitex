import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_threshold_x5f_points_x2f_statement_x2e_lit

universe u v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_4 : Litex.In _value_i3 (Litex.R (M := M))), True := by
  intro _Host_i2 _rep_i2 _value_i2 h_3 _Host_i3 _rep_i3 _value_i3 h_4
  have _struct_conditions_wd : ∀ (h_1 : Litex.Lt _value_i1 _value_i2), True := by
    intro h_1
    exact True.intro
  exact True.intro

noncomputable def _struct_base_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _struct_condition_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) (_struct_raw : M.Value) : Prop :=
  (∃ (_r _s : ℝ), (Litex.denote _value_i1) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) (Litex.CartObj M 2)) :=
  Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2) (fun _struct_value _ => ((_struct_condition_1 (M := M)) _value_i1 h_2) (Litex.denote _struct_value))

theorem _struct_members_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host : Type _} [_rep : Litex.Representation M _Host] (_struct_value : Litex.Obj (M := M) _Host) :
    Litex.In _struct_value ((struct_1 (M := M)) _value_i1 h_2) ↔ Litex.In _struct_value ((_struct_base_1 (M := M)) _value_i1 h_2) ∧ ((_struct_condition_1 (M := M)) _value_i1 h_2) (Litex.denote _struct_value) := by
  change Litex.In _struct_value (Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2) _) ↔ _
  rw [Litex.inSetBuilder_iff]
  constructor
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩

theorem h_20 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_22 : Litex.In _value_i5 ((struct_1 (M := M)) _value_i1 h_2)), Litex.In _value_i1 (Litex.R (M := M)) → Litex.In _value_i5 ((struct_1 (M := M)) _value_i1 h_2) → (∃ (_r _s : ℝ), (Litex.denote _value_i1) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i5 _rep_i5 _value_i5 h_22 _ _
          exact ((((_struct_members_1 (M := M)) _value_i1 h_2) _value_i5).mp h_22).2)
      )
  )

noncomputable def _object_w2 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w3 := ((struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))

theorem h_23 : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  let _atomic_wd_1_1 := (_object_w3 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M))
          let _atomic_wd_1_1 := (_object_w3 (M := M))
          exact (by
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (3 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_27 : (∃ (_r _s : ℝ), (Litex.denote (Litex.number (M := M) (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
            refine (((_struct_members_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 ((_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change (∃ (_r _s : ℝ), (Litex.denote (Litex.number (M := M) (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_27))
      )
  )

theorem h_31 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_45 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_51 : Litex.In _value_i7 ((struct_1 (M := M)) _value_i6 h_45)), (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt _value_i6 _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_45 _Host_i7 _rep_i7 _value_i7 h_51
          have h_52 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1)
                )
            )
          let _object_h53 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_52 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_53 : Litex.In _object_h53 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_52 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h54 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_52 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_54 : Litex.In _object_h54 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_52 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_55 : Litex.Same (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h53 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_56 : Litex.Same (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h54 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_57 : Litex.In (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_58 : Litex.In (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_59 : (∃ (_r _s : ℝ), (Litex.denote _value_i6) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i7) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).2
                )
            )
          have h_30 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Lt _value_i6 _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_45) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_45) _value_i7).mp h_51).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact h_59)
                )
            )
          exact h_30
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_threshold_x5f_points_x2f_statement_x2e_lit
