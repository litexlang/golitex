import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_parameterized_x5f_pairs_x2f_statement_x2e_lit

universe u v2 v3 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 _value_i1), True := by
  intro _Host_i2 _rep_i2 _value_i2 h_2 _Host_i3 _rep_i3 _value_i3 h_3
  exact True.intro

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

theorem h_9 : Litex.IsNonempty ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
  (by
    litex_complete =>
      exact (
        (by
          exact ⟨Litex.denote (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))), (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
            exact (Litex.tupleInCart _atomic_wd_1_0 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )))⟩
        )
      )
  )

theorem h_10 : (by
  let _atomic_wd_1_0 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
  exact Litex.IsNonempty _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
  exact (h_9 (M := M)))

variable {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))

theorem h_14 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        h_13
      )
  )

noncomputable def _object_h15 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) (h_14 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_15 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (_object_h15 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_14 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h16 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) (h_14 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_16 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (_object_h16 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_14 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_17 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.Same (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h15 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_18 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.Same (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_13 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h16 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_19 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_13 (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_20 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_13 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) h_13 (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_26 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
          exact h_13)
      )
  )

noncomputable def _object_h27 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) (h_26 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

theorem h_27 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (_object_h27 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_26 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

noncomputable def _object_h28 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) (h_26 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

theorem h_28 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (_object_h28 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_26 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_29 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.Same (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h27 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_30 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.Same (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_13 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h28 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )

theorem h_31 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
          let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
          exact h_13) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )

theorem h_32 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : Litex.In (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_13 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
          let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
          exact h_13) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_33 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.cartCall _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_13 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          exact (Litex.inOfSame (_object_h27 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13) _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) ((h_17 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_15 (M := M) (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_13)))
      )
  )

include M in
private theorem _sketch_6 {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) : True := by
  have _have_type_checks_i7 : True :=
    ((show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_43 : Litex.In _value_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))), True from by
      intro _Host_i7 _rep_i7 _value_i7 h_43
      have h_44 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
        have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) :=
        (by
          litex_checked_step =>
            exact (
              h_43
            )
        )
      let _object_h45 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
      have h_45 : Litex.In _object_h45 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_44 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      let _object_h46 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
      have h_46 : Litex.In _object_h46 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_44 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      have h_47 : Litex.Same (Litex.cartCall _value_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_43 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h45 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_48 : Litex.Same (Litex.cartCall _value_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_43 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h46 :=
        (by
          litex_checked_step =>
            exact (
              (by rfl)
            )
        )
      have h_49 : Litex.In (Litex.cartCall _value_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_43 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_43 (0 : Fin 2) (1 : ℂ) (by norm_num))
            )
        )
      have h_50 : Litex.In (Litex.cartCall _value_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_43 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_43 (1 : Fin 2) (2 : ℂ) (by norm_num))
            )
        )
      exact True.intro
    ) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (by
    let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
    let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
    exact (Litex.tupleInCart _atomic_wd_1_0 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (by
      have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
      have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    ))))
  let _object_i7 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
  have h_150 : Litex.In _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
            exact (Litex.tupleInCart _atomic_wd_1_0 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )))
        )
    )
  have h_158 : Litex.Same _object_i7 _object_i7 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))))
        )
    )
  have h_151 : Litex.In _object_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          h_150
        )
    )
  let _object_h152 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (1 : ℂ)) h_151 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_152 : Litex.In _object_h152 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_151 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h153 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (2 : ℂ)) h_151 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_153 : Litex.In _object_h153 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_151 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_154 : Litex.Same (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_150 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h152 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_155 : Litex.Same (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_150 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h153 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_156 : Litex.In (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_150 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_150 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  have h_157 : Litex.In (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_150 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_150 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_164 : Litex.In _object_i7 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
            exact h_150)
        )
    )

  let _object_h165 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (1 : ℂ)) h_164 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

  have h_165 : Litex.In _object_h165 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_164 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  let _object_h166 := (Litex.cartCall _object_i7 _ (Litex.number (M := M) (2 : ℂ)) h_164 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

  have h_166 : Litex.In _object_h166 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_164 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )

  have h_167 : Litex.Same (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_150 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h165 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_168 : Litex.Same (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_150 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h166 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )

  have h_169 : Litex.In (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_150 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
            let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
            exact h_150) (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )

  have h_170 : Litex.In (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (2 : ℂ)) h_150 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
            let _atomic_wd_1_1 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
            exact h_150) (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_42 : (by
    let _equal_wd_1_0 := (Litex.cartCall _object_i7 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.number (M := M) (1 : ℂ)) h_150 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (Eq.trans h_154 (Eq.trans (by
            let _tuple := _object_i7
            have _receiver_eq : Litex.Same _object_i7 _tuple := h_158
            have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
            have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
              simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
            have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := rfl
            exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
          ) (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_chosen_x5f_parameterized_x5f_pairs_x2f_statement_x2e_lit
