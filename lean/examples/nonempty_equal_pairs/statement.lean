import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_equal_x5f_pairs_x2f_statement_x2e_lit

universe u v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 _value_i1) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_4 : Litex.In _value_i3 _value_i1), True := by
  intro _Host_i2 _rep_i2 _value_i2 h_3 _Host_i3 _rep_i3 _value_i3 h_4
  have _struct_conditions_wd : ∀ (h_1 : Litex.Same _value_i2 _value_i3), True := by
    intro h_1
    exact True.intro
  exact True.intro

noncomputable def _struct_base_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _struct_condition_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) (_struct_raw : M.Value) : Prop :=
  ((Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) _struct_raw (M.number (2 : ℂ))))

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) (Litex.CartObj M 2)) :=
  Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2) (fun _struct_value _ => ((_struct_condition_1 (M := M)) _value_i1 h_2) (Litex.denote _struct_value))

theorem _struct_members_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) {_Host : Type _} [_rep : Litex.Representation M _Host] (_struct_value : Litex.Obj (M := M) _Host) :
    Litex.In _struct_value ((struct_1 (M := M)) _value_i1 h_2) ↔ Litex.In _struct_value ((_struct_base_1 (M := M)) _value_i1 h_2) ∧ ((_struct_condition_1 (M := M)) _value_i1 h_2) (Litex.denote _struct_value) := by
  change Litex.In _struct_value (Litex.setBuilder ((_struct_base_1 (M := M)) _value_i1 h_2) _) ↔ _
  rw [Litex.inSetBuilder_iff]
  constructor
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩
  · rintro ⟨h, law⟩
    exact ⟨h, law⟩

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.IsNonempty _value_i1) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_8 : Litex.In _value_i5 ((struct_1 (M := M)) _value_i1 h_2)), Litex.IsNonempty _value_i1 → Litex.In _value_i5 ((struct_1 (M := M)) _value_i1 h_2) → ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i5 _rep_i5 _value_i5 h_8 _ _
          exact ((((_struct_members_1 (M := M)) _value_i1 h_2) _value_i5).mp h_8).2)
      )
  )

noncomputable def _object_w1 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w2 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.standardNonempty (M := M) Litex.StandardSetValue.real))

theorem h_9 : (by
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
            have _struct_coordinate_0 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ)) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (0 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (0 : Fin 2))
                _ = _ := by rfl
            have _struct_coordinate_1 : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ)) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := by
              calc
                _ = _atomic_wd_1_0.val.values (1 : Fin 2) := by simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _atomic_wd_1_0 (1 : Fin 2))
                _ = _ := by rfl
            have h_13 : ((Litex.denote (Litex.number (M := M) (1 : ℂ))) = (Litex.denote (Litex.number (M := M) (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
            refine (((_struct_members_1 (M := M)) (Litex.R (M := M)) (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)) _atomic_wd_1_0).mpr ⟨(Litex.tupleInCart _atomic_wd_1_0 ((_struct_base_1 (M := M)) (Litex.R (M := M)) (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), ?_⟩
            change ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _atomic_wd_1_0) (M.number (2 : ℂ))))
            set_option linter.unusedSimpArgs false in
              set_option linter.unnecessarySimpa false in
                simpa only [_struct_coordinate_0, _struct_coordinate_1] using h_13))
      )
  )

theorem h_16 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_18 : Litex.IsNonempty _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_22 : Litex.In _value_i7 ((struct_1 (M := M)) _value_i6 h_18)), (by
  let _equal_wd_1_0 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  let _equal_wd_1_1 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_18 _Host_i7 _rep_i7 _value_i7 h_22
          have h_23 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote _value_i6, Litex.denote _value_i6] (by
            have _finiteProof_0 := (Litex.isSet _value_i6)
            have _finiteProof_1 := (Litex.isSet _value_i6)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1)
                )
            )
          let _object_h24 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_23 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_24 : Litex.In _object_h24 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_23 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h25 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_23 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_25 : Litex.In _object_h25 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_23 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_26 : Litex.Same (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h24 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_27 : Litex.Same (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h25 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_28 : Litex.In (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_29 : Litex.In (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_30 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i7) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i7) (M.number (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  ((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).2
                )
            )
          have h_15 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (1 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            let _equal_wd_1_1 := (Litex.cartCall _value_i7 ((_struct_base_1 (M := M)) _value_i6 h_18) (Litex.number (M := M) (2 : ℂ)) (((((_struct_members_1 (M := M)) _value_i6 h_18) _value_i7).mp h_22).1) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_30
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_equal_x5f_pairs_x2f_statement_x2e_lit
