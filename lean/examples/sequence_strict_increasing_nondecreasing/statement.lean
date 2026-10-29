import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_strict_x5f_increasing_x5f_nondecreasing_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_5)
  exact Litex.SequenceStrictlyIncreasing _value_i1)), (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_5)
  exact Litex.SequenceNondecreasing _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          let _object_h6 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_6 : Litex.In _value_i1 _object_h6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h6 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_5)
                )
            )
          have h_9 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_member_i6 : Litex.In _value_i6 (Litex.NPos (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.NPos (M := M))) (h_7 : (∃ (_r _s : ℝ), (Litex.denote _value_i6) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i6)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i7)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_member_i6 : Litex.In _value_i6 (Litex.NPos (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.NPos (M := M))) (h_7 : (∃ (_r _s : ℝ), (Litex.denote _value_i6) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s)) => (h_1) (Litex.denote _value_i6) _member_i6 (Litex.denote _value_i7) _member_i7 h_7)
                )
            )
          have h_11 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_h12 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_12 : Litex.In _value_i1 _object_h12 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h12 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_11)
                )
            )
          have h_15 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_member_i13 : Litex.In _value_i13 (Litex.NPos (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_member_i14 : Litex.In _value_i14 (Litex.NPos (M := M))) (h_13 : (∃ (_r _s : ℝ), (Litex.denote _value_i13) = M.number (_r : ℂ) ∧ (Litex.denote _value_i14) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i13)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i14)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_member_i13 : Litex.In _value_i13 (Litex.NPos (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_member_i14 : Litex.In _value_i14 (Litex.NPos (M := M))) (h_13 : (∃ (_r _s : ℝ), (Litex.denote _value_i13) = M.number (_r : ℂ) ∧ (Litex.denote _value_i14) = M.number (_s : ℂ) ∧ _r < _s)) => (h_1) (Litex.denote _value_i13) _member_i13 (Litex.denote _value_i14) _member_i14 h_13)
                )
            )
          have h_18 : Litex.SequenceNondecreasing _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_16 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                          intro _raw_i15 h_19 _
                          let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_19)
                          have h_19 : Litex.In _value_i15 (Litex.NPos (M := M)) := h_19
                          have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inNPos_positive _value_i15 h_19)
                                )
                            )
                          have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_20)
                                )
                            )
                          have h_22 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_20) _litex_zero.symm)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                                  intro _raw_i15 h_19 _
                                  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_19)
                                  have h_19 : Litex.In _value_i15 (Litex.NPos (M := M)) := h_19
                                  have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inNPos_positive _value_i15 h_19)
                                        )
                                    )
                                  have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_20)
                                        )
                                    )
                                  have h_22 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_20) _litex_zero.symm)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i1 _value_i1 _object_h12 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h12
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_12))
                          )
                      )
                    have h_17 : Litex.SequenceStrictlyIncreasing _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_35 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_member_i16 : Litex.In _value_i16 (Litex.NPos (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (_member_i17 : Litex.In _value_i17 (Litex.NPos (M := M))) (h_33 : (∃ (_r _s : ℝ), (Litex.denote _value_i16) = M.number (_r : ℂ) ∧ (Litex.denote _value_i17) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i16)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i17)) = M.number (_s : ℂ) ∧ _r < _s) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_member_i16 : Litex.In _value_i16 (Litex.NPos (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (_member_i17 : Litex.In _value_i17 (Litex.NPos (M := M))) (h_33 : (∃ (_r _s : ℝ), (Litex.denote _value_i16) = M.number (_r : ℂ) ∧ (Litex.denote _value_i17) = M.number (_s : ℂ) ∧ _r < _s)) => (h_17) (Litex.denote _value_i16) _member_i16 (Litex.denote _value_i17) _member_i17 h_33)
                          )
                      )
                    exact (show (by
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                        intro _raw_i15 h_19 _
                        let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_19)
                        have h_19 : Litex.In _value_i15 (Litex.NPos (M := M)) := h_19
                        have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i15 h_19)
                              )
                          )
                        have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_20)
                              )
                          )
                        have h_22 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_20) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                        intro _raw_i15 h_19 _
                        let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_19)
                        have h_19 : Litex.In _value_i15 (Litex.NPos (M := M)) := h_19
                        have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i15 h_19)
                              )
                          )
                        have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_20)
                              )
                          )
                        have h_22 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_20) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                        intro _raw_i15 h_19 _
                        let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_19)
                        have h_19 : Litex.In _value_i15 (Litex.NPos (M := M)) := h_19
                        have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inNPos_positive _value_i15 h_19)
                              )
                          )
                        have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_20)
                              )
                          )
                        have h_22 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_20) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_16)
                    exact Litex.SequenceNondecreasing _value_i1) from Litex.sequenceStrictOrderWeak (Litex.denote _value_i1) false (Litex.unguardedFunctionDomain _value_i1 (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) h_16) h_17)
                  )
                )
            )

          have h_38 : ∀ {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (_member_i22 : Litex.In _value_i22 (Litex.NPos (M := M))) {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_member_i23 : Litex.In _value_i23 (Litex.NPos (M := M))) (h_36 : (∃ (_r _s : ℝ), (Litex.denote _value_i22) = M.number (_r : ℂ) ∧ (Litex.denote _value_i23) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i22)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i23)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (_member_i22 : Litex.In _value_i22 (Litex.NPos (M := M))) {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_member_i23 : Litex.In _value_i23 (Litex.NPos (M := M))) (h_36 : (∃ (_r _s : ℝ), (Litex.denote _value_i22) = M.number (_r : ℂ) ∧ (Litex.denote _value_i23) = M.number (_s : ℂ) ∧ _r ≤ _s)) => (h_18) (Litex.denote _value_i22) _member_i22 (Litex.denote _value_i23) _member_i23 h_36)
                )
            )
          exact h_18
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_strict_x5f_increasing_x5f_nondecreasing_x2f_statement_x2e_lit
