import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_selected_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_2 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i2 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i2), Litex.HasSequenceLimit _value_i1 (let _sequence := _value_i1; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_6)) h_2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 h_2
          let _object_h7 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_7 : Litex.In _value_i1 _object_h7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h7 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_6)
                )
            )
          have h_24 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          let _object_h25 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_25 : Litex.In _value_i1 _object_h25 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h25 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_24)
                )
            )
          have h_33 : Litex.HasSequenceLimit _value_i1 (let _sequence := _value_i1; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_24)) h_2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_30 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                          intro _raw_i16 h_34 _
                          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                          have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                          have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i16 h_34)
                                )
                            )
                          have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                                )
                            )
                          have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
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
                                  intro _raw_i16 h_34 _
                                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                                  have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                                  have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i16 h_34)
                                        )
                                    )
                                  have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                                        )
                                    )
                                  have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h25 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h25
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_25))
                          )
                      )
                    have h_32 : ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_46 : Litex.In _value_i17 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i17 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    exact (show (by
                    let _atomic_wd_1_1 := (let _sequence := _value_i1; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_34 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                        have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_34)
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                              )
                          )
                        have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_34 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                        have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_34)
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                              )
                          )
                        have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_30)) h_32)
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_34 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                        have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_34)
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                              )
                          )
                        have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_34 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                        have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_34)
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                              )
                          )
                        have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                        intro _raw_i16 h_34 _
                        let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                        have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i16 h_34)
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                              )
                          )
                        have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_30)
                    have _sequence_limit_real : Litex.In _atomic_wd_1_1 (Litex.R (M := M)) := (Litex.sequenceLimitInR _atomic_wd_1_1)
                    exact Litex.HasSequenceLimit _value_i1 _atomic_wd_1_1) from Litex.sequenceLimitSelected (let _sequence := _value_i1; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                      intro _raw_i16 h_34 _
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                      have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                      have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inNPos_positive _value_i16 h_34)
                            )
                        )
                      have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                            )
                        )
                      have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i16 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i16 : M.Value) => True) _raw_i16) → True := (by
                      intro _raw_i16 h_34 _
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_34)
                      have h_34 : Litex.In _value_i16 (Litex.NPos (M := M)) := h_34
                      have h_35 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inNPos_positive _value_i16 h_34)
                            )
                        )
                      have h_36 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_35)
                            )
                        )
                      have h_37 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_35) _litex_zero.symm)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_30)) h_32))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (let _sequence := _value_i1; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_24)) h_2)
            exact h_33)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_selected_x5f_by_x5f_theorem_x2f_statement_x2e_lit
