import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_unique_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_7)
  have _sequence_limit_real : Litex.In _value_i2 (Litex.R (M := M)) := h_9
  exact Litex.HasSequenceLimit _value_i1 _value_i2)) (h_2 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_7)
  have _sequence_limit_real : Litex.In _value_i3 (Litex.R (M := M)) := h_10
  exact Litex.HasSequenceLimit _value_i1 _value_i3)), Litex.Same _value_i2 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i3 _rep_i3 _value_i3 h_10 h_1 h_2
          let _object_h8 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_8 : Litex.In _value_i1 _object_h8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h8 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_7)
                )
            )
          have h_25 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_27 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_28 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          let _object_h26 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_26 : Litex.In _value_i1 _object_h26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h26 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_25)
                )
            )
          have h_5 : Litex.Same _value_i2 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_42 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                          intro _raw_i14 h_46 _
                          let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_46)
                          have h_46 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_46
                          have h_47 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i14 h_46)
                                )
                            )
                          have h_48 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_47)
                                )
                            )
                          have h_49 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_47) _litex_zero.symm)
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
                                  intro _raw_i14 h_46 _
                                  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_46)
                                  have h_46 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_46
                                  have h_47 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i14 h_46)
                                        )
                                    )
                                  have h_48 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_47)
                                        )
                                    )
                                  have h_49 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_47) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h26 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h26
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_26))
                          )
                      )
                    have h_43 : Litex.HasSequenceLimit _value_i1 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_44 : Litex.HasSequenceLimit _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_45 : Litex.Same _value_i2 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show Litex.Same _value_i2 _value_i3 from Litex.sequenceLimitCandidatesEqual _value_i1 _value_i2 _value_i3 (Litex.unguardedFunctionDomain _value_i1 (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) h_42) h_27 h_28 h_43 h_44)
                          )
                      )
                    exact (Eq.trans (Eq.symm (Litex.sameRefl _value_i2)) (Eq.trans h_45 (Litex.sameRefl _value_i3)))
                  )
                )
            )
          exact h_5
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_unique_x5f_by_x5f_theorem_x2f_statement_x2e_lit
