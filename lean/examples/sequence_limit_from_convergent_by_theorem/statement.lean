import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_from_x5f_convergent_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_6)
  exact Litex.SequenceConvergent _value_i1)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_10 : Litex.In _value_i2 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 h_1
          let _object_h7 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_7 : Litex.In _value_i1 _object_h7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h7 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_6)
                )
            )
          have h_9 : (∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i1) (Litex.denote _value_i7))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          have h_15 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          let _object_h16 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_16 : Litex.In _value_i1 _object_h16 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h16 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_15)
                )
            )
          have h_18 : (∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i1) (Litex.denote _value_i13))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          have h_22 : ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_43 : Litex.In _value_i15 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_19 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                          intro _raw_i14 h_23 _
                          let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_23)
                          have h_23 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_23
                          have h_24 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i14 h_23)
                                )
                            )
                          have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_24)
                                )
                            )
                          have h_26 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_24) _litex_zero.symm)
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
                                  intro _raw_i14 h_23 _
                                  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_23)
                                  have h_23 : Litex.In _value_i14 (Litex.NPos (M := M)) := h_23
                                  have h_24 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i14 h_23)
                                        )
                                    )
                                  have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_24)
                                        )
                                    )
                                  have h_26 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_24) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h16 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h16
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_16))
                          )
                      )
                    have h_20 : Litex.SequenceConvergent _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_38 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i1) (Litex.denote _value_i16))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_20
                          )
                      )
                    exact (show ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_39 : Litex.In _value_i15 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i15 from h_20)
                  )
                )
            )
          exact h_18
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_from_x5f_convergent_x5f_by_x5f_theorem_x2f_statement_x2e_lit
