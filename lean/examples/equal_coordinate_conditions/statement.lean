import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_coordinate_x5f_conditions_x2f_statement_x2e_lit

universe u v1 v2 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))), True := by
  intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3
  have _struct_conditions_wd : ∀ (h_1 : Litex.Same _value_i1 _value_i2), True := by
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
  ((Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (2 : ℂ))))

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

theorem h_5 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_6 : Litex.In _value_i4 (struct_1 (M := M))), Litex.In _value_i4 (struct_1 (M := M)) → ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (M.number (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_6 _
          exact (((_struct_members_1 (M := M)) _value_i4).mp h_6).2)
      )
  )

noncomputable def _object_w2 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w3 := (struct_1 (M := M))

theorem h_7 : (by
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
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_10 : ((Litex.denote (Litex.number (M := M) (2 : ℂ))) = (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
            refine ((_struct_members_1 (M := M)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 (_struct_base_1 (M := M)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ))))
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_10))
      )
  )

theorem h_13 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_26 : Litex.In _value_i5 (_object_w3 (M := M))), (by
  let _equal_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  let _equal_wd_1_1 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_26
          have h_27 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1)
                )
            )
          let _object_h28 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_27 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_28 : Litex.In _object_h28 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_27 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h29 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_27 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_29 : Litex.In _object_h29 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_27 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_30 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h28 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_31 : Litex.Same (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h29 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_32 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_33 : Litex.In (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_34 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (((_struct_members_1 (M := M)) _value_i5).mp h_26).2
                )
            )
          have h_12 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            let _equal_wd_1_1 := (Litex.cartCall _value_i5 (_struct_base_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) ((((_struct_members_1 (M := M)) _value_i5).mp h_26).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_34
                )
            )
          exact h_12
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_coordinate_x5f_conditions_x2f_statement_x2e_lit
