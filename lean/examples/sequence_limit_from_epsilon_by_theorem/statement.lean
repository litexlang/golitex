import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (Litex.R (M := M))) (h_5 : (by
  let _object_h11 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_11 : Litex.In _value_i1 _object_h11 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h11 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10)
        )
    )
  exact ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_13 : Litex.In _value_i3 (Litex.RPos (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_17 : Litex.In _value_i4 (Litex.NPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_21 : Litex.In _value_i5 (Litex.NPos (M := M))) => Litex.Le _value_i4 _value_i5)) (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_150 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_150) (M.real_subset_complex _ h_12));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.subInR _value_i6 _value_i2 h_150 h_12)))) _value_i3));
  (by
    have _preimage_target : (by
    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_564 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_564) (M.real_subset_complex _ h_12));
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.subInR _value_i6 _value_i2 h_564 h_12)))) _value_i3))
    exact Litex.IsSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_564 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_564) (M.real_subset_complex _ h_12));
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.subInR _value_i6 _value_i2 h_564 h_12)))) _value_i3))
    exact (Litex.isSet _atomic_wd_1_0))
    let _preimage_builder := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_978 : Litex.In _value_i10 (Litex.NPos (M := M))) => Litex.In (let _litex_call_arg_0 := _value_i10;
  Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 h_11 h_978 True.intro) _wd_1_1))
    exact Litex.preimageSet _wd_1_0 _wd_1_1 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (Litex.inOfSame _wd_1_0 _wd_1_0 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_10)))
)), (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_10)
  have _sequence_limit_real : Litex.In _value_i2 (Litex.R (M := M)) := h_12
  exact Litex.HasSequenceLimit _value_i1 _value_i2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i2 _rep_i2 _value_i2 h_12 h_5
          let _object_h11 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_11 : Litex.In _value_i1 _object_h11 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h11 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_10)
                )
            )
          have h_1476 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1478 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          let _object_h1477 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_1477 : Litex.In _value_i1 _object_h1477 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h1477 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_1476)
                )
            )
          have h_8 : Litex.HasSequenceLimit _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2936 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                          intro _raw_i16 h_2944 _
                          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                          have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                          have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i16 h_2944)
                                )
                            )
                          have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                                )
                            )
                          have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                                  intro _raw_i16 h_2944 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                                  have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                                  have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_2944)
                                        )
                                    )
                                  have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                                        )
                                    )
                                  have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h1477 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1477
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_1477))
                          )
                      )
                    have h_2937 : Litex.In _value_i2 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1478
                          )
                      )
                    have h_2942 : ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_2970 : Litex.In _value_i17 (Litex.RPos (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_2974 : Litex.In _value_i18 (Litex.NPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_2978 : Litex.In _value_i19 (Litex.NPos (M := M))) => Litex.Le _value_i18 _value_i19)) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_3131 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i2 (M.real_subset_complex _ h_3131) (M.real_subset_complex _ h_2937));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i20 _value_i2 h_3131 h_2937)))) _value_i17));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_3643 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i2 (M.real_subset_complex _ h_3643) (M.real_subset_complex _ h_2937));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i20 _value_i2 h_3643 h_2937)))) _value_i17))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_3643 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i2 (M.real_subset_complex _ h_3643) (M.real_subset_complex _ h_2937));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i20 _value_i2 h_3643 h_2937)))) _value_i17))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_4155 : Litex.In _value_i22 (Litex.NPos (M := M))) => Litex.In (let _litex_call_arg_0 := _value_i22;
                    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 h_2936 h_4155 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_2944 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                        have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                        have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_2944)
                              )
                          )
                        have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                              )
                          )
                        have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_2944 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                        have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                        have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_2944)
                              )
                          )
                        have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                              )
                          )
                        have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2936))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i17 _rep_i17 _value_i17 h_2970
                              have h_2971 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i17 h_2970)
                                    )
                                )
                              have h_2972 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i17 h_2971)
                                    )
                                )
                              have h_2973 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i17 h_2971) _litex_zero.symm)
                                    )
                                )
                              exact (h_5 _value_i17 h_2970)
                            )
                          )
                      )
                    have h_2943 : Litex.HasSequenceLimit _value_i1 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                                  intro _raw_i16 h_2944 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                                  have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                                  have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_2944)
                                        )
                                    )
                                  have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                                        )
                                    )
                                  have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                                  intro _raw_i16 h_2944 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                                  have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                                  have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_2944)
                                        )
                                    )
                                  have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                                        )
                                    )
                                  have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                                  intro _raw_i16 h_2944 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_2944)
                                  have h_2944 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_2944
                                  have h_2945 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_2944)
                                        )
                                    )
                                  have h_2946 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_2945)
                                        )
                                    )
                                  have h_2947 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_2945) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2936)
                              have _sequence_limit_real : Litex.In _value_i2 (Litex.R (M := M)) := h_2937
                              exact Litex.HasSequenceLimit _value_i1 _value_i2) from Litex.sequenceLimitOfForall _value_i1 _value_i2 h_2942)
                          )
                      )
                    exact h_2943
                  )
                )
            )
          exact h_8
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
