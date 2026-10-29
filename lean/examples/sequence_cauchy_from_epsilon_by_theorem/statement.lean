import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_6 : (by
  let _object_h11 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_11 : Litex.In _value_i1 _object_h11 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h11 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10)
        )
    )
  exact ∀ (_value_i2 : Litex.Obj (M := M) M.Value) (h_12 : Litex.In _value_i2 (Litex.RPos (M := M))), ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_16 : Litex.In _value_i3 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_20 : Litex.In _value_i4 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i4));
  let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_137 : Litex.In _value_i5 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i5));
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_254 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
    let _object_h255 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_254 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_255 : Litex.In _object_h255 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_254 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h256 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_254 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_256 : Litex.In _object_h256 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_254 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h255;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_11 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_255) True.intro));
    let _wd_2_1 := (let _wd_3_0 := _object_h256;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_11 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_256) True.intro));
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
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_10)
  exact Litex.SequenceCauchy _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 h_6
          let _object_h11 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_11 : Litex.In _value_i1 _object_h11 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h11 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10)
                )
            )
          have h_2561 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          let _object_h2562 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_2562 : Litex.In _value_i1 _object_h2562 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h2562 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_2561)
                )
            )
          have h_5112 : Litex.SequenceCauchy _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_5111 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                          intro _raw_i14 h_5118 _
                          let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_5118)
                          have h_5118 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_5118
                          have h_5119 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i14 h_5118)
                                )
                            )
                          have h_5120 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_5119)
                                )
                            )
                          have h_5121 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_5119) _litex_zero.symm)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                                  intro _raw_i14 h_5118 _
                                  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_5118)
                                  have h_5118 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_5118
                                  have h_5119 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i14 h_5118)
                                        )
                                    )
                                  have h_5120 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_5119)
                                        )
                                    )
                                  have h_5121 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_5119) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h2562 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h2562
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_2562))
                          )
                      )
                    have h_5117 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_5135 : Litex.In _value_i15 (Litex.RPos (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_5139 : Litex.In _value_i16 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_5143 : Litex.In _value_i17 (Litex.NPos (M := M))) => Litex.Le _value_i16 _value_i17));
                    let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_5272 : Litex.In _value_i17 (Litex.NPos (M := M))) => Litex.Le _value_i16 _value_i17));
                    (let _productChild_0 := _wd_1_0;
                    let _productChild_1 := _wd_1_1;
                    Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                      have _finiteProof_0 := ((Litex.isSet _productChild_0))
                      have _finiteProof_1 := ((Litex.isSet _productChild_1))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_5401 : Litex.In _value_i18 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                      let _object_h5402 := (Litex.cartCall _value_i18 _ (Litex.number (M := M) (1 : ℂ)) h_5401 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                      have h_5402 : Litex.In _object_h5402 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5401 (0 : Fin 2) (1 : ℂ) (by norm_num))
                            )
                        )
                      let _object_h5403 := (Litex.cartCall _value_i18 _ (Litex.number (M := M) (2 : ℂ)) h_5401 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                      have h_5403 : Litex.In _object_h5403 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5401 (1 : Fin 2) (2 : ℂ) (by norm_num))
                            )
                        )
                      exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h5402;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_5111 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_5402) True.intro));
                      let _wd_2_1 := (let _wd_3_0 := _object_h5403;
                      (let _litex_call_arg_0 := _wd_3_0;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_5111 (by
                        let _atomic_wd_1_0 := _wd_3_0
                        exact h_5403) True.intro));
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
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))))) _value_i15
                    ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i15 _rep_i15 _value_i15 h_5135
                              have h_5136 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i15 h_5135)
                                    )
                                )
                              have h_5137 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_5136)
                                    )
                                )
                              have h_5138 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_5136) _litex_zero.symm)
                                    )
                                )
                              exact (h_6 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_5135)
                            )
                          )
                      )
                    exact (show (by
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                        intro _raw_i14 h_5118 _
                        let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_5118)
                        have h_5118 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_5118
                        have h_5119 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i14 h_5118)
                              )
                          )
                        have h_5120 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_5119)
                              )
                          )
                        have h_5121 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_5119) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                        intro _raw_i14 h_5118 _
                        let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_5118)
                        have h_5118 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_5118
                        have h_5119 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i14 h_5118)
                              )
                          )
                        have h_5120 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_5119)
                              )
                          )
                        have h_5121 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_5119) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                        intro _raw_i14 h_5118 _
                        let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_5118)
                        have h_5118 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_5118
                        have h_5119 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i14 h_5118)
                              )
                          )
                        have h_5120 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_5119)
                              )
                          )
                        have h_5121 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_5119) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_5111)
                    exact Litex.SequenceCauchy _value_i1) from Litex.sequenceCauchyOfForall _value_i1 h_5117)
                  )
                )
            )

          have h_7989 : ∀ {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.RPos (M := M))), (∃ (_value_i25 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i25) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i26 : M.Value) => ∃ (_ : M.mem _raw_i26 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i25) = M.number (_r : ℂ) ∧ _raw_i26 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i26 : M.Value) => ∃ (_ : M.mem _raw_i26 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i25) = M.number (_r : ℂ) ∧ _raw_i26 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i27 : M.Value) => ∃ (_ : M.mem _raw_i27 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i27 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i27 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i24) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.RPos (M := M))) => (h_5112) (Litex.denote _value_i24) _member_i24)
                )
            )
          exact h_5112
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
