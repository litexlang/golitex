import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_designated_x5f_coordinate_x5f_pairs_x2f_statement_x2e_lit

universe u v3 v4 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) : ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_4 : Litex.In _value_i3 _value_i1) {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_5 : Litex.In _value_i4 _value_i1), True := by
  intro _Host_i3 _rep_i3 _value_i3 h_4 _Host_i4 _rep_i4 _value_i4 h_5
  have _struct_conditions_wd : ∀ (h_1 : Litex.Same _value_i3 _value_i2), True := by
    intro h_1
    exact True.intro
  exact True.intro

noncomputable def _struct_base_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _struct_condition_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) (_struct_raw : M.Value) : Prop :=
  ((Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = (Litex.denote _value_i2))

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) (Litex.CartObj M 2)) :=
  Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2 _value_i2 h_3) (fun _struct_value _ => ((_struct_condition_1 (M := M)) _value_i1 h_2 _value_i2 h_3) (Litex.denote _struct_value))

theorem _struct_members_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) {_Host : Type _} [_rep : Litex.Representation M _Host] (_struct_value : Litex.Obj (M := M) _Host) :
    Litex.In _struct_value ((struct_1 (M := M)) _value_i1 h_2 _value_i2 h_3) ↔ Litex.In _struct_value ((_struct_base_1 (M := M)) _value_i1 h_2 _value_i2 h_3) ∧ ((_struct_condition_1 (M := M)) _value_i1 h_2 _value_i2 h_3) (Litex.denote _struct_value) := by
  change Litex.In _struct_value (Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2 _value_i2 h_3) _) ↔ _
  rw [Litex.inSetBuilder_iff]
  constructor
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_10 : Litex.In _value_i6 ((struct_1 (M := M)) _value_i1 h_2 _value_i2 h_3)), Litex.IsSet _value_i1 → Litex.In _value_i2 _value_i1 → Litex.In _value_i6 ((struct_1 (M := M)) _value_i1 h_2 _value_i2 h_3) → ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (M.number (1 : ℂ))) = (Litex.denote _value_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3 _Host_i6 _rep_i6 _value_i6 h_10 _ _ _
          exact ((((_struct_members_1 (M := M)) _value_i1 h_2 _value_i2 h_3) _value_i6).mp h_10).2)
      )
  )

noncomputable def _object_w1 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w2 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))

theorem h_11 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact (by
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (3 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_16 : ((Litex.denote (Litex.number (M := M) (2 : ℂ))) = (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
            refine (((_struct_members_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 ((_struct_base_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = (Litex.denote (Litex.number (M := M) (2 : ℂ))))
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_16))
      )
  )

theorem h_19 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_22 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_23 : Litex.In _value_i8 _value_i7) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_32 : Litex.In _value_i9 ((struct_1 (M := M)) _value_i7 h_22 _value_i8 h_23)), (by
  let _equal_wd_1_0 := (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _value_i8) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_22 _Host_i8 _rep_i8 _value_i8 h_23 _Host_i9 _rep_i9 _value_i9 h_32
          have h_33 : Litex.In _value_i9 (Litex.cart (M := M) ![Litex.denote _value_i7, Litex.denote _value_i7] (by
            have _finiteProof_0 := (Litex.isSet _value_i7)
            have _finiteProof_1 := (Litex.isSet _value_i7)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1)
                )
            )
          let _object_h34 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (1 : ℂ)) h_33 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_34 : Litex.In _object_h34 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_33 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h35 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (2 : ℂ)) h_33 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_35 : Litex.In _object_h35 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_33 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_36 : Litex.Same (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h34 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_37 : Litex.Same (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h35 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_38 : Litex.In (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_39 : Litex.In (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_40 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i9) (M.number (1 : ℂ))) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).2
                )
            )
          have h_18 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i9 ((_struct_base_1 (M := M)) _value_i7 h_22 _value_i8 h_23) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i7 h_22 _value_i8 h_23) _value_i9).mp h_32).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.Same _equal_wd_1_0 _value_i8) :=
            (by
              litex_checked_step =>
                exact (
                  h_40
                )
            )
          exact h_18
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_designated_x5f_coordinate_x5f_pairs_x2f_statement_x2e_lit
