import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_origin_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit

universe u v1 v2
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

include M in
theorem _have_type_checks_i5 : True :=
  ((show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3 : Litex.In _value_i5 (struct_1 (M := M))), True from by
    intro _Host_i5 _rep_i5 _value_i5 h_3
    have h_4 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
      have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) :=
      (by
        litex_checked_step =>
          exact (
            h_3
          )
      )
    let _object_h5 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_4 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_5 : Litex.In _object_h5 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h6 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_4 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_6 : Litex.In _object_h6 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_7 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_3 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h5 :=
      (by
        litex_checked_step =>
          exact (
            (by rfl)
          )
      )
    have h_8 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_3 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h6 :=
      (by
        litex_checked_step =>
          exact (
            (by rfl)
          )
      )
    have h_9 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_3 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_3 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    have h_10 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_3 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_3 (1 : Fin 2) (2 : ℂ) (by norm_num))
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
noncomputable def _object_i5 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i))))
theorem h_14 : Litex.In (_object_i5 (M := M)) (struct_1 (M := M)) :=
  (by
    litex_complete =>
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
theorem h_22 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (0 : ℂ)), Litex.denote (Litex.number (M := M) (0 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (0 : ℂ))) (fun i => Fin.elim0 i)))))
      )
  )
theorem h_15 : Litex.In (_object_i5 (M := M)) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) :=
  (by
    litex_complete =>
      exact (
        (h_14 (M := M))
      )
  )
noncomputable def _object_h16 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (1 : ℂ)) (h_15 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
theorem h_16 : Litex.In (_object_h16 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_15 (M := M)) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )
noncomputable def _object_h17 := (Litex.cartCall (_object_i5 (M := M)) _ (Litex.number (M := M) (2 : ℂ)) (h_15 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
theorem h_17 : Litex.In (_object_h17 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_15 (M := M)) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )
theorem h_18 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (_object_h16 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )
theorem h_19 : Litex.Same (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (_object_h17 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rfl)
      )
  )
theorem h_20 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_14 (M := M)) (0 : Fin 2) (1 : ℂ) (by norm_num))
      )
  )
theorem h_21 : Litex.In (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.FiniteFunction.coordinate_mem_number (M := M) (h_14 (M := M)) (1 : Fin 2) (2 : ℂ) (by norm_num))
      )
  )

theorem h_23 : (by
  let _equal_wd_1_0 := (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_18 (M := M)) (Eq.trans (by
          let _tuple := (_object_i5 (M := M))
          have _receiver_eq : Litex.Same (_object_i5 (M := M)) _tuple := (h_22 (M := M))
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
          have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.number (M := M) (0 : ℂ)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        ) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_38 : (by
  let _equal_wd_1_0 := (Litex.cartCall (_object_i5 (M := M)) (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_14 (M := M)) (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_19 (M := M)) (Eq.trans (by
          let _tuple := (_object_i5 (M := M))
          have _receiver_eq : Litex.Same (_object_i5 (M := M)) _tuple := (h_22 (M := M))
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
          have _target_eq : _tuple.val.values (1 : Fin 2) = Litex.denote (Litex.number (M := M) (0 : ℂ)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        ) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_origin_x5f_coordinate_x5f_fields_x2f_statement_x2e_lit
