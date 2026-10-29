import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_tail_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_11 : Litex.In _value_i2 (Litex.RPos (M := M))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_9)
  exact Litex.SequenceCauchy _value_i1)), (by
  let _object_h10 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_10 : Litex.In _value_i1 _object_h10 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h10 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_9)
        )
    )
  exact ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_20 : Litex.In _value_i3 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_24 : Litex.In _value_i4 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i4));
  let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_141 : Litex.In _value_i5 (Litex.NPos (M := M))) => Litex.Le _value_i3 _value_i5));
  (let _productChild_0 := _wd_1_0;
  let _productChild_1 := _wd_1_1;
  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
    have _finiteProof_0 := ((Litex.isSet _productChild_0))
    have _finiteProof_1 := ((Litex.isSet _productChild_1))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_258 : Litex.In _value_i6 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
    let _object_h259 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_258 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_259 : Litex.In _object_h259 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_258 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h260 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_258 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_260 : Litex.In _object_h260 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_258 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h259;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_10 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_259) True.intro));
    let _wd_2_1 := (let _wd_3_0 := _object_h260;
    (let _litex_call_arg_0 := _wd_3_0;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_10 (by
      let _atomic_wd_1_0 := _wd_3_0
      exact h_260) True.intro));
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
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 _Host_i2 _rep_i2 _value_i2 h_11 h_1
          let _object_h10 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_10 : Litex.In _value_i1 _object_h10 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h10 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_9)
                )
            )
          have h_12 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_11)
                )
            )
          have h_13 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_12)
                )
            )
          have h_14 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_12) _litex_zero.symm)
                )
            )
          have h_19 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_member_i11 : Litex.In _value_i11 (Litex.RPos (M := M))), (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i12) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i13 : M.Value) => ∃ (_ : M.mem _raw_i13 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i12) = M.number (_r : ℂ) ∧ _raw_i13 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i13 : M.Value) => ∃ (_ : M.mem _raw_i13 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i12) = M.number (_r : ℂ) ∧ _raw_i13 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i14 : M.Value) => ∃ (_ : M.mem _raw_i14 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i14 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i14 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i11) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_member_i11 : Litex.In _value_i11 (Litex.RPos (M := M))) => (h_1) (Litex.denote _value_i11) _member_i11)
                )
            )
          have h_2565 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_2567 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          let _object_h2566 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_2566 : Litex.In _value_i1 _object_h2566 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h2566 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_2565)
                )
            )
          have h_2568 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_2567)
                )
            )
          have h_2569 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_2568)
                )
            )
          have h_2570 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_2568) _litex_zero.symm)
                )
            )
          have h_2575 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_member_i19 : Litex.In _value_i19 (Litex.RPos (M := M))), (∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i20) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i21 : M.Value) => ∃ (_ : M.mem _raw_i21 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i20) = M.number (_r : ℂ) ∧ _raw_i21 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i21 : M.Value) => ∃ (_ : M.mem _raw_i21 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i20) = M.number (_r : ℂ) ∧ _raw_i21 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i22 : M.Value) => ∃ (_ : M.mem _raw_i22 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i22 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i22 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i19) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_member_i19 : Litex.In _value_i19 (Litex.RPos (M := M))) => (h_1) (Litex.denote _value_i19) _member_i19)
                )
            )
          have h_2582 : ∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (h_5775 : Litex.In _value_i24 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_5779 : Litex.In _value_i25 (Litex.NPos (M := M))) => Litex.Le _value_i24 _value_i25));
          let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_5896 : Litex.In _value_i25 (Litex.NPos (M := M))) => Litex.Le _value_i24 _value_i25));
          (let _productChild_0 := _wd_1_0;
          let _productChild_1 := _wd_1_1;
          Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
            have _finiteProof_0 := ((Litex.isSet _productChild_0))
            have _finiteProof_1 := ((Litex.isSet _productChild_1))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i26 : Litex.Obj (M := M) M.Value) (h_6013 : Litex.In _value_i26 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
            let _object_h6014 := (Litex.cartCall _value_i26 _ (Litex.number (M := M) (1 : ℂ)) h_6013 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
            have h_6014 : Litex.In _object_h6014 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6013 (0 : Fin 2) (1 : ℂ) (by norm_num))
                  )
              )
            let _object_h6015 := (Litex.cartCall _value_i26 _ (Litex.number (M := M) (2 : ℂ)) h_6013 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
            have h_6015 : Litex.In _object_h6015 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.FiniteFunction.coordinate_mem_number (M := M) h_6013 (1 : Fin 2) (2 : ℂ) (by norm_num))
                  )
              )
            exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h6014;
            (let _litex_call_arg_0 := _wd_3_0;
            Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2566 (by
              let _atomic_wd_1_0 := _wd_3_0
              exact h_6014) True.intro));
            let _wd_2_1 := (let _wd_3_0 := _object_h6015;
            (let _litex_call_arg_0 := _wd_3_0;
            Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2566 (by
              let _atomic_wd_1_0 := _wd_3_0
              exact h_6015) True.intro));
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
          ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2576 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → True := (by
                          intro _raw_i23 h_2583 _
                          let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2583)
                          have h_2583 : Litex.In _value_i23 (Litex.NPos (M := M)) := h_2583
                          have h_2584 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i23 h_2583)
                                )
                            )
                          have h_2585 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i23 h_2584)
                                )
                            )
                          have h_2586 : ¬ Litex.Same _value_i23 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i23 h_2584) _litex_zero.symm)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → True := (by
                                  intro _raw_i23 h_2583 _
                                  let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2583)
                                  have h_2583 : Litex.In _value_i23 (Litex.NPos (M := M)) := h_2583
                                  have h_2584 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i23 h_2583)
                                        )
                                    )
                                  have h_2585 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i23 h_2584)
                                        )
                                    )
                                  have h_2586 : ¬ Litex.Same _value_i23 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i23 h_2584) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h2566 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h2566
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_2566))
                          )
                      )
                    have h_2577 : Litex.SequenceCauchy _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_2601 : ∀ {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (_member_i27 : Litex.In _value_i27 (Litex.RPos (M := M))), (∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i28) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i29 : M.Value) => ∃ (_ : M.mem _raw_i29 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i28) = M.number (_r : ℂ) ∧ _raw_i29 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i29 : M.Value) => ∃ (_ : M.mem _raw_i29 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i28) = M.number (_r : ℂ) ∧ _raw_i29 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i30 : M.Value) => ∃ (_ : M.mem _raw_i30 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i30 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i30 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i27) = M.number (_s : ℂ) ∧ _r < _s))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (_member_i27 : Litex.In _value_i27 (Litex.RPos (M := M))) => (h_2577) (Litex.denote _value_i27) _member_i27)
                          )
                      )
                    have h_2578 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2567
                          )
                      )
                    have h_2612 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i2 h_2578)
                          )
                      )
                    have h_2613 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_2612)
                          )
                      )
                    have h_2614 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_2612) _litex_zero.symm)
                          )
                      )
                    exact (show ∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (h_2615 : Litex.In _value_i24 (Litex.NPos (M := M))), Litex.Subset (let _wd_1_0 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_2619 : Litex.In _value_i25 (Litex.NPos (M := M))) => Litex.Le _value_i24 _value_i25));
                  let _wd_1_1 := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_2760 : Litex.In _value_i25 (Litex.NPos (M := M))) => Litex.Le _value_i24 _value_i25));
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.cart (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i26 : Litex.Obj (M := M) M.Value) (h_2901 : Litex.In _value_i26 (Litex.cart (M := M) ![Litex.denote (Litex.NPos (M := M)), Litex.denote (Litex.NPos (M := M))] (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (Fin.cases (Litex.isSet (Litex.NPos (M := M))) (fun i => Fin.elim0 i))))) => (by
                    let _object_h2902 := (Litex.cartCall _value_i26 _ (Litex.number (M := M) (1 : ℂ)) h_2901 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
                    have h_2902 : Litex.In _object_h2902 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2901 (0 : Fin 2) (1 : ℂ) (by norm_num))
                          )
                      )
                    let _object_h2903 := (Litex.cartCall _value_i26 _ (Litex.number (M := M) (2 : ℂ)) h_2901 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
                    have h_2903 : Litex.In _object_h2903 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2901 (1 : Fin 2) (2 : ℂ) (by norm_num))
                          )
                      )
                    exact Litex.Lt (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h2902;
                    (let _litex_call_arg_0 := _wd_3_0;
                    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2576 (by
                      let _atomic_wd_1_0 := _wd_3_0
                      exact h_2902) True.intro));
                    let _wd_2_1 := (let _wd_3_0 := _object_h2903;
                    (let _litex_call_arg_0 := _wd_3_0;
                    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_2576 (by
                      let _atomic_wd_1_0 := _wd_3_0
                      exact h_2903) True.intro));
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
                  ))) from (by
                    obtain ⟨_cutoff, _member, _control⟩ := h_2577 (Litex.denote _value_i2) h_2578
                    exact ⟨_cutoff, _member, _control⟩
                  ))
                  )
                )
            )
          exact h_2582
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_cauchy_x5f_tail_x5f_by_x5f_theorem_x2f_statement_x2e_lit
