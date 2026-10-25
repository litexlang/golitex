import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_point_x5f_conditions_x2f_statement_x2e_lit

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

noncomputable def _object_w2 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w3 := (struct_1 (M := M))

theorem h_17 : (by
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
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_20))
      )
  )

theorem h_24 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_37 : Litex.In _value_i5 (_object_w3 (M := M))), (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_37
          have h_38 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1)
                )
            )
          let _object_h39 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_38 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_39 : Litex.In _object_h39 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_38 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h40 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_38 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_40 : Litex.In _object_h40 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_38 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_41 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h39 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_42 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h40 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_43 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_44 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_45 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (((_struct_members_1 (M := M)) _value_i5).mp h_37).2
                )
            )
          have h_23 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_37).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact h_45)
                )
            )
          exact h_23
        )
      )
  )

theorem h_52 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_65 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (h_50 : (by
  let _object_h66 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_65 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact (by
    let _atomic_wd_1_0 := _object_h66
    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)
)), (by
  let _atomic_wd_1_1 := (_object_w3 (M := M))
  exact Litex.In _value_i6 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_65 h_50
          let _object_h66 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_65 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_66 : Litex.In _object_h66 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_65 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h67 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_65 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_67 : Litex.In _object_h67 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_65 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_51 : (by
            let _atomic_wd_1_1 := (_object_w3 (M := M))
            exact Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (_object_w3 (M := M))
                    exact (by
                      have h_109 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _object_h66) = M.number (_s : ℂ) ∧ _r < _s) := (by
                        let _atomic_wd_2_0 := _object_h66
                        exact h_50)
                      refine ((_struct_members_1 (M := M)) _value_i6).mpr ⟨(show Litex.In _value_i6 (_struct_base_1 (M := M)) from (by
                      let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_65)), ?_⟩
                      change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_109))
                )
            )
          exact h_51
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_point_x5f_conditions_x2f_statement_x2e_lit
