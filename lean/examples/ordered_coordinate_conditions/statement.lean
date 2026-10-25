import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_coordinate_x5f_conditions_x2f_statement_x2e_lit

universe u v1 v2 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))), True := by
  intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3
  have _struct_conditions_wd : ∀ (h_1 : ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1) ∧ (Litex.Lt _value_i1 _value_i2))), True := by
    intro h_1
    have h_28 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (And.left h_1)
          )
      )
    have h_29 : Litex.Lt _value_i1 _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (And.right h_1)
          )
      )
    exact True.intro
  exact True.intro

noncomputable def _struct_base_1 : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _struct_condition_1 (_struct_raw : M.Value) : Prop :=
  (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)))

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

theorem h_31 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_32 : Litex.In _value_i4 (struct_1 (M := M))), Litex.In _value_i4 (struct_1 (M := M)) → (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_32 _
          exact (((_struct_members_1 (M := M)) _value_i4).mp h_32).2)
      )
  )

noncomputable def _object_w2 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w3 := (struct_1 (M := M))

theorem h_33 : (by
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
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_36 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.denote (Litex.number (M := M) (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.denote (Litex.number (M := M) (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s))) := (And.intro ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
            refine ((_struct_members_1 (M := M)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 (_struct_base_1 (M := M)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)))
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_36))
      )
  )

theorem h_45 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_58 : Litex.In _value_i5 (_object_w3 (M := M))), (((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)) ∧ ((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  let _atomic_wd_1_1 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_58
          have h_59 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1)
                )
            )
          let _object_h60 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_59 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_60 : Litex.In _object_h60 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_59 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h61 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_59 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_61 : Litex.In _object_h61 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_59 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_62 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h60 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_63 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h61 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_64 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_65 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_66 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s))) :=
            (by
              litex_checked_step =>
                exact (
                  (((_struct_members_1 (M := M)) _value_i5).mp h_58).2
                )
            )
          have h_67 :=
            (And.left h_66)
          have h_68 :=
            (And.right h_66)
          have h_69 :=
            h_67
          have h_70 :=
            h_68
          have h_96 :=
            (Litex.ltTrans (Litex.number (M := M) (0 : ℂ)) (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_67 h_68)
          have h_43 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact h_67)
                )
            )
          have h_44 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            let _atomic_wd_1_1 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    let _atomic_wd_1_1 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_58).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    exact h_68)
                )
            )
          exact (And.intro h_43 h_44)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_coordinate_x5f_conditions_x2f_statement_x2e_lit
