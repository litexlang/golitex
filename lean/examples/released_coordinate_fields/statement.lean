import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit

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

theorem h_7 : (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact Litex.IsNonempty _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (struct_1 (M := M))
  exact (h_6 (M := M)))

variable {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M)))

theorem h_11 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        h_10
      )
  )

noncomputable def _object_h12 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) (h_11 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_12 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h12 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_11 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h13 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) (h_11 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_13 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h13 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_11 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_14 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h12 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_15 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h13 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_16 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10 (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_17 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10 (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_23 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_10)
      )
  )

noncomputable def _object_h24 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) (h_23 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_24 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h24 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_23 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h25 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) (h_23 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_25 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (_object_h25 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_23 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_26 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h24 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_27 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h25 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_28 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_10) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_29 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
          let _atomic_wd_1_1 := (struct_1 (M := M))
          exact h_10) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_30 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_10 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          exact (Litex.inOfSame (_object_h24 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) ((h_14 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_12 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10)))
      )
  )

theorem h_39 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (struct_1 (M := M))) : (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_10 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          exact (Litex.inOfSame (_object_h25 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10) _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) ((h_15 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_13 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_10)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit
