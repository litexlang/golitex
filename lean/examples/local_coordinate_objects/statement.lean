import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_coordinate_x5f_objects_x2f_statement_x2e_lit

universe u v1 v2 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 (Litex.R (M := M))), True := by
  intro _Host_i1 _rep_i1 _value_i1 h_1 _Host_i2 _rep_i2 _value_i2 h_2
  exact True.intro

noncomputable def struct_1 : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

theorem h_6 : Litex.IsNonempty (struct_1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          exact ⟨Litex.denote (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))), (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact (Litex.tupleInCart _atomic_wd_1_0 (struct_1 (M := M)) (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )))⟩
        )
      )
  )

include M in
private theorem _sketch_3 : True := by
  have h_9 : (by
    let _atomic_wd_1_0 := (struct_1 (M := M))
    exact Litex.IsNonempty _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (struct_1 (M := M))
    exact (h_6 (M := M)))

  obtain ⟨_witness_i5, _member_i5⟩ := h_9

  let _value_i5 := Litex.semanticObject (M := M) _witness_i5 (M.member_isSet _member_i5)

  have h_12 : Litex.In _value_i5 (struct_1 (M := M)) := _member_i5

  have h_13 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          h_12
        )
    )

  let _object_h14 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

  have h_14 : Litex.In _object_h14 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_13 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  let _object_h15 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_13 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

  have h_15 : Litex.In _object_h15 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_13 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_16 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h14 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_17 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_12 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h15 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_18 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_12 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  have h_19 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_12 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_12 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_25 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_12)
        )
    )

  let _object_h26 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_25 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

  have h_26 : Litex.In _object_h26 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_25 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  let _object_h27 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_25 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

  have h_27 : Litex.In _object_h27 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_25 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_28 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h26 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_29 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_12 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h27 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_30 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_12) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  have h_31 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_12 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact h_12) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_7 : (by
    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_12 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact (Litex.inOfSame _object_h26 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_16).symm (show @Eq M.Value _ _ from Eq.refl _) h_14))
        )
    )
  have _have_type_checks_i6 : True :=
    ((show ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_40 : Litex.In _value_i6 (struct_1 (M := M))), True from by
      intro _Host_i6 _rep_i6 _value_i6 h_40
      have h_41 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
        have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) :=
        (by
          litex_checked_step =>
            exact (
              h_40
            )
        )
      let _object_h42 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_41 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
      have h_42 : Litex.In _object_h42 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_41 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      let _object_h43 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_41 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
      have h_43 : Litex.In _object_h43 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_41 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_44 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_40 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h42 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_45 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_40 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h43 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_46 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_40 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_40 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      have h_47 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_40 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_40 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      exact True.intro
    ) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i)))) (by
    let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i))))
    let _atomic_wd_1_1 := (struct_1 (M := M))
    exact (Litex.tupleInCart _atomic_wd_1_0 (struct_1 (M := M)) (by
      have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
      have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    ))))
  let _object_i6 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i))))
  have h_147 : Litex.In _object_i6 (struct_1 (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (struct_1 (M := M))
            exact (Litex.tupleInCart _atomic_wd_1_0 (struct_1 (M := M)) (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )))
        )
    )
  have h_155 : Litex.Same _object_i6 _object_i6 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i)))))
        )
    )
  have h_148 : Litex.In _object_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          h_147
        )
    )
  let _object_h149 := (Litex.cartCall _object_i6 _ (Litex.number (M := M) (1 : ℂ)) h_148 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_149 : Litex.In _object_h149 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_148 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h150 := (Litex.cartCall _object_i6 _ (Litex.number (M := M) (2 : ℂ)) h_148 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_150 : Litex.In _object_h150 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_148 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_151 : Litex.Same (Litex.cartCall _object_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_147 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h149 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_152 : Litex.Same (Litex.cartCall _object_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_147 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h150 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_153 : Litex.In (Litex.cartCall _object_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_147 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_147 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  have h_154 : Litex.In (Litex.cartCall _object_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_147 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_147 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_8 : (by
    let _equal_wd_1_0 := (Litex.cartCall _object_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_147 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (Eq.trans h_151 (Eq.trans (by
            let _tuple := _object_i6
            have _receiver_eq : Litex.Same _object_i6 _tuple := h_155
            have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
            have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
              simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
            have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.number (M := M) (0 : ℂ)) := rfl
            exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
          ) (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_coordinate_x5f_objects_x2f_statement_x2e_lit
