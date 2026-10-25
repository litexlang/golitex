import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_parameterized_x5f_pairs_x2f_statement_x2e_lit

universe u v2 v3 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem _struct_field_checks_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsNonempty _value_i1) : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 _value_i1), True := by
  intro _Host_i2 _rep_i2 _value_i2 h_2 _Host_i3 _rep_i3 _value_i3 h_3
  exact True.intro

noncomputable def struct_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsNonempty _value_i1) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

noncomputable def _object_w1 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w2 := ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.standardNonempty (M := M) Litex.StandardSetValue.real))

theorem h_4 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact (Litex.tupleInCart _atomic_wd_1_0 ((struct_1 (M := M)) (Litex.R (M := M)) (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)) (by
            have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
            have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )))
      )
  )

theorem h_11 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.IsNonempty _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_17 : Litex.In _value_i7 ((struct_1 (M := M)) _value_i6 h_13)), ((Litex.IsNonempty _value_i6) ∧ ((((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 _value_i6)) ∧ ((by
  let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact Litex.In _atomic_wd_1_0 _value_i6))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_13 _Host_i7 _rep_i7 _value_i7 h_17
          have h_18 : Litex.In _value_i7 (Litex.cart (M := M) ![Litex.denote _value_i6, Litex.denote _value_i6] (by
            have _finiteProof_0 := (Litex.isSet _value_i6)
            have _finiteProof_1 := (Litex.isSet _value_i6)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          let _object_h19 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_19 : Litex.In _object_h19 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h20 := (Litex.cartCall _value_i7 _ (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_20 : Litex.In _object_h20 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_21 : Litex.Same (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h19 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_22 : Litex.Same (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h20 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_23 : Litex.In (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_24 : Litex.In (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_8 : Litex.IsNonempty _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_9 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact (Litex.inOfSame _object_h19 _atomic_wd_1_0 _value_i6 _value_i6 (h_21).symm (show @Eq M.Value _ _ from Eq.refl _) h_19))
                )
            )
          have h_10 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i7 ((struct_1 (M := M)) _value_i6 h_13) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    exact (Litex.inOfSame _object_h20 _atomic_wd_1_0 _value_i6 _value_i6 (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20))
                )
            )
          exact (And.intro h_8 (And.intro h_9 h_10))
        )
      )
  )

theorem h_47 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_48 : Litex.IsNonempty _value_i8), ((Litex.IsSet _value_i8) ∧ (Litex.IsNonempty _value_i8)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_48
          have h_45 : Litex.IsSet _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet _value_i8)
                )
            )
          have h_46 : Litex.IsNonempty _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_48
                )
            )
          exact (And.intro h_45 h_46)
        )
      )
  )

theorem h_53 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_56 : Litex.IsNonempty _value_i9), ((Litex.IsSet _value_i9) ∧ (Litex.IsNonempty _value_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_56
          exact ((h_47 (M := M)) _value_i9 h_56)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_parameterized_x5f_pairs_x2f_statement_x2e_lit
