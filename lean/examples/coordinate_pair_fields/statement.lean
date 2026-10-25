import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_pair_x5f_fields_x2f_statement_x2e_lit

universe u v1 v2 v5 v6
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

theorem h_5 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_18 : Litex.In _value_i5 (struct_1 (M := M))), (by
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
  let _object_h21 := (Litex.cartCall _value_i5 _ (Litex.number (M := M) (2 : ℂ)) h_19 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  exact (((by
    let _equal_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    let _equal_wd_1_1 := _object_h20
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    let _equal_wd_1_1 := _object_h21
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_18
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
          have h_3 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            let _equal_wd_1_1 := _object_h20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_4 : (by
            let _equal_wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            let _equal_wd_1_1 := _object_h21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_23
                )
            )
          exact (And.intro h_3 h_4)
        )
      )
  )

theorem h_31 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_44 : Litex.In _value_i6 (struct_1 (M := M))), (by
  have h_45 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          h_44
        )
    )
  let _object_h46 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_45 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
  have h_46 : Litex.In _object_h46 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_45 (0 : Fin 2) (1 : ℂ) (by norm_num))
        )
    )
  let _object_h47 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_45 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_47 : Litex.In _object_h47 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_45 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_48 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h46 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_49 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h47 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  let _object_w16 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
  let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h46 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_48).symm (show @Eq M.Value _ _ from Eq.refl _) h_46))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h47 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_49).symm (show @Eq M.Value _ _ from Eq.refl _) h_47)))))
  let _object_w17 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
  let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h47 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_49).symm (show @Eq M.Value _ _ from Eq.refl _) h_47))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h46 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_48).symm (show @Eq M.Value _ _ from Eq.refl _) h_46)))))
  exact (((by
    let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _equal_wd_1_0 := _object_w16
    let _equal_wd_1_1 := _object_w17
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_44
          have h_45 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  h_44
                )
            )
          let _object_h46 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_45 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_46 : Litex.In _object_h46 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_45 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h47 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_45 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_47 : Litex.In _object_h47 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_45 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_48 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h46 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_49 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h47 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_50 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_44 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_51 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_44 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_28 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    exact (Litex.inOfSame _object_h46 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_48).symm (show @Eq M.Value _ _ from Eq.refl _) h_46))
                )
            )
          have h_29 : (by
            let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    exact (Litex.inOfSame _object_h47 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_49).symm (show @Eq M.Value _ _ from Eq.refl _) h_47))
                )
            )
          let _object_w16 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
          let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h46 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_48).symm (show @Eq M.Value _ _ from Eq.refl _) h_46))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h47 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_49).symm (show @Eq M.Value _ _ from Eq.refl _) h_47)))))
          let _object_w17 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
          let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h47 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_49).symm (show @Eq M.Value _ _ from Eq.refl _) h_47))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h46 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_48).symm (show @Eq M.Value _ _ from Eq.refl _) h_46)))))
          have h_30 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w16;
                  let _equal_wd_1_1 := _object_w17;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_50)) + (Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_51))) ((Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_51)) + (Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_50))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_50)) (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_51))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_44 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_51)) (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_44 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_50))) (by ring!))))
                )
            )
          exact (And.intro h_28 (And.intro h_29 h_30))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_pair_x5f_fields_x2f_statement_x2e_lit
