import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_tail_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.In _value_i3 (Litex.RPos (M := M))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_8)
  have _sequence_limit_real : Litex.In _value_i2 (Litex.R (M := M)) := h_10
  exact Litex.HasSequenceLimit _value_i1 _value_i2)), (by
  let _object_h9 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_9 : Litex.In _value_i1 _object_h9 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h9 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_8)
        )
    )
  exact ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_20 : Litex.In _value_i4 (Litex.NPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_24 : Litex.In _value_i5 (Litex.NPos (M := M))) => Litex.Le _value_i4 _value_i5)) (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_153 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_153) (M.real_subset_complex _ h_10));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.subInR _value_i6 _value_i2 h_153 h_10)))) _value_i3));
  (by
    have _preimage_target : (by
    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_561 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_561) (M.real_subset_complex _ h_10));
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.subInR _value_i6 _value_i2 h_561 h_10)))) _value_i3))
    exact Litex.IsSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_561 : Litex.In _value_i6 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i6 _value_i2 (M.real_subset_complex _ h_561) (M.real_subset_complex _ h_10));
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.subInR _value_i6 _value_i2 h_561 h_10)))) _value_i3))
    exact (Litex.isSet _atomic_wd_1_0))
    let _preimage_builder := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_969 : Litex.In _value_i12 (Litex.NPos (M := M))) => Litex.In (let _litex_call_arg_0 := _value_i12;
  Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 h_9 h_969 True.intro) _wd_1_1))
    exact Litex.preimageSet _wd_1_0 _wd_1_1 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (Litex.inOfSame _wd_1_0 _wd_1_0 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_8)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_11 h_1
          let _object_h9 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_9 : Litex.In _value_i1 _object_h9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h9 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_8)
                )
            )
          have h_12 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i3 h_11)
                )
            )
          have h_13 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_12)
                )
            )
          have h_14 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_12) _litex_zero.symm)
                )
            )
          have h_1456 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_1458 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1459 : Litex.In _value_i3 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          let _object_h1457 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_1457 : Litex.In _value_i1 _object_h1457 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h1457 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_1456)
                )
            )
          have h_1460 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i3 h_1459)
                )
            )
          have h_1461 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_1460)
                )
            )
          have h_1462 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_1460) _litex_zero.symm)
                )
            )
          have h_1474 : ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_3327 : Litex.In _value_i17 (Litex.NPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_3331 : Litex.In _value_i18 (Litex.NPos (M := M))) => Litex.Le _value_i17 _value_i18)) (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_3460 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_3460) (M.real_subset_complex _ h_1458));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i19 _value_i2 h_3460 h_1458)))) _value_i3));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_3868 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_3868) (M.real_subset_complex _ h_1458));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i19 _value_i2 h_3868 h_1458)))) _value_i3))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_3868 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_3868) (M.real_subset_complex _ h_1458));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i19 _value_i2 h_3868 h_1458)))) _value_i3))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_4276 : Litex.In _value_i23 (Litex.NPos (M := M))) => Litex.In (let _litex_call_arg_0 := _value_i23;
          Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 h_1457 h_4276 True.intro) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) => True) _litex_input)) (Litex.inOfSame _wd_1_0 _wd_1_0 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_1456))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1468 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                          intro _raw_i16 h_1475 _
                          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_1475)
                          have h_1475 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_1475
                          have h_1476 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i16 h_1475)
                                )
                            )
                          have h_1477 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_1476)
                                )
                            )
                          have h_1478 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_1476) _litex_zero.symm)
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
                                  intro _raw_i16 h_1475 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_1475)
                                  have h_1475 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_1475
                                  have h_1476 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_1475)
                                        )
                                    )
                                  have h_1477 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_1476)
                                        )
                                    )
                                  have h_1478 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_1476) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h1457 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1457
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_1457))
                          )
                      )
                    have h_1469 : Litex.HasSequenceLimit _value_i1 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1470 : Litex.In _value_i3 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1459
                          )
                      )
                    have h_1503 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i3 h_1470)
                          )
                      )
                    have h_1504 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_1503)
                          )
                      )
                    have h_1505 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_1503) _litex_zero.symm)
                          )
                      )
                    exact (show ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_1506 : Litex.In _value_i17 (Litex.NPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_1510 : Litex.In _value_i18 (Litex.NPos (M := M))) => Litex.Le _value_i17 _value_i18)) (let _wd_1_0 := _value_i1;
                  let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_1663 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_1663) (M.real_subset_complex _ h_1458));
                  (Litex.abs _wd_2_0 (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.subInR _value_i19 _value_i2 h_1663 h_1458)))) _value_i3));
                  (by
                    have _preimage_target : (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_2191 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_2191) (M.real_subset_complex _ h_1458));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i19 _value_i2 h_2191 h_1458)))) _value_i3))
                    exact Litex.IsSet _atomic_wd_1_0) := (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_2191 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i2 (M.real_subset_complex _ h_2191) (M.real_subset_complex _ h_1458));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i19 _value_i2 h_2191 h_1458)))) _value_i3))
                    exact (Litex.isSet _atomic_wd_1_0))
                    let _preimage_builder := (Litex.setBuilder (Litex.NPos (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_2719 : Litex.In _value_i21 (Litex.NPos (M := M))) => Litex.In (let _litex_call_arg_0 := _value_i21;
                  Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 h_1468 h_2719 True.intro) _wd_1_1))
                    exact Litex.preimageSet _wd_1_0 _wd_1_1 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                      intro _raw_i16 h_1475 _
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_1475)
                      have h_1475 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_1475
                      have h_1476 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inNPos_positive _value_i16 h_1475)
                            )
                        )
                      have h_1477 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_1476)
                            )
                        )
                      have h_1478 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_1476) _litex_zero.symm)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                      intro _raw_i16 h_1475 _
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_1475)
                      have h_1475 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_1475
                      have h_1476 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inNPos_positive _value_i16 h_1475)
                            )
                        )
                      have h_1477 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_1476)
                            )
                        )
                      have h_1478 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_1476) _litex_zero.symm)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1468))) from (by
                    obtain ⟨_limit_cutoff, _limit_cutoff_member, _limit_control⟩ := Litex.sequenceLimitTail _value_i1 _value_i2 _value_i3 h_1469 h_1470
                    refine ⟨_limit_cutoff, _limit_cutoff_member, ?_⟩
                    exact _limit_control
                  ))
                  )
                )
            )
          exact h_1474
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_tail_x5f_by_x5f_theorem_x2f_statement_x2e_lit
