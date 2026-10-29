import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2 v33 v34
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_6 : (by
  let _object_h12 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_12 : Litex.In _value_i1 _object_h12 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h12 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_11)
        )
    )
  exact ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_13 : Litex.In _value_i2 (Litex.RPos (M := M))), ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_17 : Litex.In _value_i3 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_21 : Litex.In _value_i4 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i4));
  let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_138 : Litex.In _value_i5 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i5));
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_255 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
    let _object_h256 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_255 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_256 : Litex.In _object_h256 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_255 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h257 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_255 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_257 : Litex.In _object_h257 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_255 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h256;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_12 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_256) True.intro));
    let _wd_2_1 := (let _wd_3_0 := _object_h257;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_12 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_257) True.intro));
    (Litex.sub _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
        let _litex_return_call := (_atomic_wd_1_0).val.left
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
        let _litex_return_call := (_atomic_wd_1_0).val.right
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i2
  )))
)), (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_11)
  exact Litex.SequenceCauchy _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 h_6
          let _object_h12 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_12 : Litex.In _value_i1 _object_h12 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h12 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_11)
                )
            )
          have h_2562 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          let _object_h2563 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_2563 : Litex.In _value_i1 _object_h2563 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h2563 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_2562)
                )
            )
          have h_9 : (by
            have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_2562)
            exact Litex.SequenceCauchy _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_2562)
                    exact (Litex.sequenceCauchyOfForall _value_i1 (show ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_5122 : Litex.In _value_i16 (Litex.RPos (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_5126 : Litex.In _value_i17 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_5130 : Litex.In _value_i18 (Litex.NPos (M := M))) => Litex.Le _value_i17 _value_i18));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_5247 : Litex.In _value_i18 (Litex.NPos (M := M))) => Litex.Le _value_i17 _value_i18));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_5364 : Litex.In _value_i19 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h5365 := (Litex.cartCall _value_i19 _ (Litex.number (M := M) (1 : ℂ)) h_5364 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_5365 : Litex.In _object_h5365 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5364 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h5366 := (Litex.cartCall _value_i19 _ (Litex.number (M := M) (2 : ℂ)) h_5364 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_5366 : Litex.In _object_h5366 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5364 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h5365;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2563 (by
                        let _atomic_wd_2_0 := _wd_3_0
                        exact h_5365) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h5366;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2563 (by
                        let _atomic_wd_2_0 := _wd_3_0
                        exact h_5366) True.intro));
                      (Litex.sub _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0))) (by
                        let _atomic_wd_2_0 := _wd_2_1
                        exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_2_0 := _wd_1_0
                        exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (by
                          let _litex_return_call := (_atomic_wd_2_0).val.left
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                          let _litex_return_call := (_atomic_wd_2_0).val.right
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i16
                    ))) from (by
                      intro _Host_i16 _rep_i16 _value_i16 h_5122
                      have h_5123 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i16 h_5122)
                            )
                        )
                      have h_5124 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_5123)
                            )
                        )
                      have h_5125 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_5123) _litex_zero.symm)
                            )
                        )
                      exact (h_6 _value_i16 h_5122)
                    ))))
                )
            )

          have h_7674 : ∀ {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.RPos (M := M))), (∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i26) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i27 : M.Value) => ∃ (_ : M.mem _raw_i27 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i26) = M.number (_r : ℂ) ∧ _raw_i27 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i27 : M.Value) => ∃ (_ : M.mem _raw_i27 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i26) = M.number (_r : ℂ) ∧ _raw_i27 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i28 : M.Value) => ∃ (_ : M.mem _raw_i28 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i28 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i28 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i25) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.RPos (M := M))) => (h_9) (Litex.denote _value_i25) _member_i25)
                )
            )
          exact h_9
        )
      )
  )

theorem h_10234 : ∀ {_Host_i33 : Type v33} [_rep_i33 : Litex.Representation M _Host_i33] (_value_i33 : Litex.Obj (M := M) _Host_i33) (h_10266 : Litex.In _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i34 : Type v34} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_10268 : Litex.In _value_i34 (Litex.RPos (M := M))) (h_10228 : (by
  have _sequence_domain : Litex.In _value_i33 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i33 _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_10266)
  exact Litex.SequenceCauchy _value_i33)), (by
  let _object_h10267 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_10267 : Litex.In _value_i33 _object_h10267 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i33 _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h10267 (Litex.sameRefl _value_i33) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10266)
        )
    )
  exact ∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_10277 : Litex.In _value_i35 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
  let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
    let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_10516) True.intro));
    let _wd_2_1 := (let _wd_3_0 := _object_h10517;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_10517) True.intro));
    (Litex.sub _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
        let _litex_return_call := (_atomic_wd_1_0).val.left
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
        let _litex_return_call := (_atomic_wd_1_0).val.right
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
  )))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i33 _rep_i33 _value_i33 h_10266 _Host_i34 _rep_i34 _value_i34 h_10268 h_10228
          let _object_h10267 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_10267 : Litex.In _value_i33 _object_h10267 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i33 _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h10267 (Litex.sameRefl _value_i33) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10266)
                )
            )
          have h_10269 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i34 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i34 h_10268)
                )
            )
          have h_10270 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i34 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i34 h_10269)
                )
            )
          have h_10271 : ¬ Litex.Same _value_i34 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i34 h_10269) _litex_zero.symm)
                )
            )
          have h_10276 : ∀ {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (_member_i42 : Litex.In _value_i42 (Litex.RPos (M := M))), (∃ (_value_i43 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i43) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i44 : M.Value) => ∃ (_ : M.mem _raw_i44 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i43) = M.number (_r : ℂ) ∧ _raw_i44 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i44 : M.Value) => ∃ (_ : M.mem _raw_i44 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i43) = M.number (_r : ℂ) ∧ _raw_i44 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i45 : M.Value) => ∃ (_ : M.mem _raw_i45 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i33) (Litex.FunctionSemantics.callValue (M := M) _raw_i45 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i33) (Litex.FunctionSemantics.callValue (M := M) _raw_i45 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i42) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (_member_i42 : Litex.In _value_i42 (Litex.RPos (M := M))) => (h_10228) (Litex.denote _value_i42) _member_i42)
                )
            )
          have h_10233 : ∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_10277 : Litex.In _value_i35 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
          let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
          (let _productChild_0 := _wd_1_0;
          let _productChild_1 := _wd_1_1;
          Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
            have _finiteProof_0 := ((Litex.isSet _productChild_0))
            have _finiteProof_1 := ((Litex.isSet _productChild_1))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
            let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
                  )
              )
            let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
                  )
              )
            exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
            (let _litex_call_arg_0 := _wd_3_0;
            Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
              let _atomic_wd_1_0 := _wd_3_0
              exact h_10516) True.intro));
            let _wd_2_1 := (let _wd_3_0 := _object_h10517;
            (let _litex_call_arg_0 := _wd_3_0;
            Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
              let _atomic_wd_1_0 := _wd_3_0
              exact h_10517) True.intro));
            (Litex.sub _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                let _litex_return_call := (_atomic_wd_1_0).val.left
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                let _litex_return_call := (_atomic_wd_1_0).val.right
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
          ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_12842 : Litex.In _value_i34 (Litex.RPos (M := M)) :=
                      h_10268
                    rcases (h_10276 _value_i34 h_12842) with ⟨_value_i35, h_10277, h_10232⟩
                    have h_10278 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inNPos_positive _value_i35 h_10277)
                          )
                      )
                    have h_10279 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i35 h_10278)
                          )
                      )
                    have h_10280 : ¬ Litex.Same _value_i35 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i35 h_10278) _litex_zero.symm)
                          )
                      )
                    have _exist_match_0 : Litex.Same (Litex.NPos (M := M)) (Litex.NPos (M := M)) := (Litex.sameRefl (Litex.NPos (M := M)))
                    have _exist_match_1 : Litex.Same (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) := (by
                      let _left := (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )))
                      let _right := (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_10281 : Litex.In _value_i36 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i36));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_10398 : Litex.In _value_i37 (Litex.NPos (M := M))) => Litex.Le _value_i35 _value_i37));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )))
                      exact (show Litex.Same _left _right from rfl))
                    have _exist_match_2 : Litex.Same (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10516) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h10517;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10517) True.intro));
                      (Litex.sub _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_1_0 := _wd_2_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                          let _litex_return_call := (_atomic_wd_1_0).val.left
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                          let _litex_return_call := (_atomic_wd_1_0).val.right
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
                    ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10516) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h10517;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10517) True.intro));
                      (Litex.sub _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_1_0 := _wd_2_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                          let _litex_return_call := (_atomic_wd_1_0).val.left
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                          let _litex_return_call := (_atomic_wd_1_0).val.right
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
                    ))) := (by
                      let _left := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10516) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h10517;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10517) True.intro));
                      (Litex.sub _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_1_0 := _wd_2_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                          let _litex_return_call := (_atomic_wd_1_0).val.left
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                          let _litex_return_call := (_atomic_wd_1_0).val.right
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
                    )))
                      let _right := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_10515 : Litex.In _value_i38 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h10516 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (1 : ℂ)) h_10515 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_10516 : Litex.In _object_h10516 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h10517 := (Litex.cartCall _value_i38 _ (Litex.number (M := M) (2 : ℂ)) h_10515 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_10517 : Litex.In _object_h10517 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_10515 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h10516;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10516) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h10517;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) => True) _litex_input) _value_i33 _litex_call_arg_0 h_10267 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_10517) True.intro));
                      (Litex.sub _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_1_0 := _wd_2_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (by
                        let _atomic_wd_1_0 := _wd_2_1
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (by
                          let _litex_return_call := (_atomic_wd_1_0).val.left
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)) (by
                          let _litex_return_call := (_atomic_wd_1_0).val.right
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i34
                    )))
                      exact (show Litex.Same _left _right from rfl))
                    exact ⟨_value_i35, h_10277, h_10232⟩
                  )
                )
            )
          exact h_10233
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_definition_x2f_statement_x2e_lit
