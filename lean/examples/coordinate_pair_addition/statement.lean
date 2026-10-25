import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_pair_x5f_addition_x2f_statement_x2e_lit

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

theorem h_4 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_17 : Litex.In _value_i5 (struct_1 (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_18 : Litex.In _value_i6 (struct_1 (M := M))), (by
  have h_19 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
    have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) :=
    (by
      litex_checked_step =>
        exact (
          h_17
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
  have h_22 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h20 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  have h_26 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
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
  let _object_h28 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_26 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
  have h_28 : Litex.In _object_h28 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.FiniteFunction.coordinate_mem_number (M := M) h_26 (1 : Fin 2) (2 : ℂ) (by norm_num))
        )
    )
  have h_30 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h28 :=
    (by
      litex_checked_step =>
        exact (
          (by rfl)
        )
    )
  let _object_w13 := (let _wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
  let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h20 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h28 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_30).symm (show @Eq M.Value _ _ from Eq.refl _) h_28)))))
  let _object_w14 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
  let _wd_1_1 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h28 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_30).symm (show @Eq M.Value _ _ from Eq.refl _) h_28))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (Litex.inOfSame _object_h20 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20)))))
  exact (by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_17 _Host_i6 _rep_i6 _value_i6 h_18
          have h_19 : Litex.In _value_i5 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.R (M := M)))
            have _finiteProof_1 := (Litex.isSet (Litex.R (M := M)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
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
          have h_22 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h20 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_23 : Litex.Same (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h21 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_24 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_25 : Litex.In (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_26 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (by
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
          let _object_h27 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_26 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_27 : Litex.In _object_h27 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_26 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h28 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_26 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_28 : Litex.In _object_h28 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_26 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_29 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_30 : Litex.Same (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) _object_h28 :=
            (by
              litex_checked_step =>
                exact (
                  (by rfl)
                )
            )
          have h_31 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_18 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          have h_32 : Litex.In (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_18 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_w13 := (let _wd_1_0 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
          let _wd_1_1 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h20 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h28 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_30).symm (show @Eq M.Value _ _ from Eq.refl _) h_28)))))
          let _object_w14 := (let _wd_1_0 := (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))));
          let _wd_1_1 := (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h28 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_30).symm (show @Eq M.Value _ _ from Eq.refl _) h_28))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (Litex.inOfSame _object_h20 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_22).symm (show @Eq M.Value _ _ from Eq.refl _) h_20)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_24)) + (Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_32))) ((Litex.NativeBridge.asComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_32)) + (Litex.NativeBridge.asComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_24))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_24)) (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_32))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i6 (struct_1 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_18 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2)))) h_32)) (Litex.NativeBridge.asComplex_spec (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) (Litex.realToComplex (Litex.cartCall _value_i5 (struct_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2)))) h_24))) (by ring!))))
                )
            )
          exact h_3
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_coordinate_x5f_pair_x5f_addition_x2f_statement_x2e_lit
