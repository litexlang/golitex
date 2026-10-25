import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_field_x5f_theorem_x2f_statement_x2e_lit

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

theorem h_4 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_6 : Litex.In _value_i5 (struct_1 (M := M))), (by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_6 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_6
          have h_7 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          let _object_h8 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_7 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_8 : Litex.In _object_h8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_7 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h9 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_7 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_9 : Litex.In _object_h9 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_7 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_10 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_6 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h8 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_11 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_6 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h9 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_12 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_6 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_13 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_6 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_18 : Litex.In _value_i5 (struct_1 (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_19 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          let _object_h20 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_19 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_20 : Litex.In _object_h20 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_19 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h21 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_19 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_21 : Litex.In _object_h21 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_19 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_22 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h20 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_23 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h21 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_24 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_25 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_31 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (struct_1 (M := M))
                    exact h_18)
                )
            )

          let _object_h32 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (1 : ℂ)) h_31 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

          have h_32 : Litex.In _object_h32 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_31 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )

          let _object_h33 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_31 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

          have h_33 : Litex.In _object_h33 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_31 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )

          have h_34 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h32 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )

          have h_35 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )

          have h_36 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
                    let _atomic_wd_1_1 := (struct_1 (M := M))
                    exact h_18) (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )

          have h_37 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) (by
                    let _atomic_wd_1_1 := (struct_1 (M := M))
                    exact h_18) (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_5 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact (Litex.inOfSame _object_h32 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20))
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact (Litex.inOfSame _object_h32 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_field_x5f_theorem_x2f_statement_x2e_lit
