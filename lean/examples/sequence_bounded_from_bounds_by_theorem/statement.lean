import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_bounded_x5f_from_x5f_bounds_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) (h_3 : (by
  let _object_h8 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_8 : Litex.In _value_i1 _object_h8 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h8 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_7)
        )
    )
  exact ∀ (_value_i4 : Litex.Obj (M := M) M.Value) (h_11 : Litex.In _value_i4 (Litex.NPos (M := M))), (((by
    let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i4;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_8 h_11 True.intro)
    exact Litex.Le _value_i2 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i4;
    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_8 h_11 True.intro)
    exact Litex.Le _atomic_wd_1_0 _value_i3)))
)), (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_7)
  exact Litex.SequenceBounded _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i3 _rep_i3 _value_i3 h_10 h_3
          let _object_h8 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_8 : Litex.In _value_i1 _object_h8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h8 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_7)
                )
            )
          have h_274 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_276 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_277 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          let _object_h275 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_275 : Litex.In _value_i1 _object_h275 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h275 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_274)
                )
            )
          have h_546 : Litex.SequenceBounded _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_540 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                          intro _raw_i10 h_547 _
                          let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_547)
                          have h_547 : Litex.In _value_i10 (Litex.NPos (M := M)) := h_547
                          have h_548 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i10 h_547)
                                )
                            )
                          have h_549 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_548)
                                )
                            )
                          have h_550 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_548) _litex_zero.symm)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                                  intro _raw_i10 h_547 _
                                  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_547)
                                  have h_547 : Litex.In _value_i10 (Litex.NPos (M := M)) := h_547
                                  have h_548 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i10 h_547)
                                        )
                                    )
                                  have h_549 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_548)
                                        )
                                    )
                                  have h_550 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_548) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h275 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h275
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_275))
                          )
                      )
                    have h_541 : Litex.In _value_i2 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_276
                          )
                      )
                    have h_542 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_277
                          )
                      )
                    have h_545 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_585 : Litex.In _value_i11 (Litex.NPos (M := M))), ((Litex.Le _value_i2 (let _litex_call_arg_0 := _value_i11;
                    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_540 h_585 True.intro)) ∧ (Litex.Le (let _litex_call_arg_0 := _value_i11;
                    Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_540 h_585 True.intro) _value_i3)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_585
                              have h_586 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inNPos_positive _value_i11 h_585)
                                    )
                                )
                              have h_587 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i11 h_586)
                                    )
                                )
                              have h_588 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i11 h_586) _litex_zero.symm)
                                    )
                                )
                              exact (h_3 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_585)
                            )
                          )
                      )
                    exact (show (by
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_547 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_547)
                        have h_547 : Litex.In _value_i10 (Litex.NPos (M := M)) := h_547
                        have h_548 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i10 h_547)
                              )
                          )
                        have h_549 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_548)
                              )
                          )
                        have h_550 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_548) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_547 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_547)
                        have h_547 : Litex.In _value_i10 (Litex.NPos (M := M)) := h_547
                        have h_548 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i10 h_547)
                              )
                          )
                        have h_549 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_548)
                              )
                          )
                        have h_550 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_548) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_547 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_547)
                        have h_547 : Litex.In _value_i10 (Litex.NPos (M := M)) := h_547
                        have h_548 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i10 h_547)
                              )
                          )
                        have h_549 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_548)
                              )
                          )
                        have h_550 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_548) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_540)
                    exact Litex.SequenceBounded _value_i1) from Litex.sequenceBoundedFromPointwise _value_i1 _value_i2 _value_i3 (Litex.unguardedFunctionDomain _value_i1 (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) h_540) h_541 h_542 (by
                    intro n hn
                    exact h_545 (Litex.semanticObject n (M.member_isSet hn)) hn
                  ))
                  )
                )
            )

          have h_953 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1))) :=
            (by
              litex_checked_step =>
                exact (
                  h_546
                )
            )

          have h_955 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1)) (Litex.denote _value_i16))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_546).1
                )
            )

          have h_957 : (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i17) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1)) (Litex.denote _value_i17))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_546).2
                )
            )

          have h_958 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i1)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_546).2
                )
            )

          have h_959 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i1)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_546).1
                )
            )
          exact h_546
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_bounded_x5f_from_x5f_bounds_x5f_by_x5f_theorem_x2f_statement_x2e_lit
