import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_property_x5f_citations_x2f_statement_x2e_lit

universe u v1 v2 v11 v12 v17 v18 v27 v28 v33 v34 v43 v44 v49 v50 v59 v60 v65 v66 v73 v74 v79 v80 v87 v88 v93 v94 v103 v104
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_24 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_1 : Litex.Same _value_i1 _value_i2) (h_2 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_24)
  exact Litex.SequenceNondecreasing _value_i1)), Litex.SequenceNondecreasing _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_24 _Host_i2 _rep_i2 _value_i2 h_26 h_1 h_2
          let _object_h25 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_25 : Litex.In _value_i1 _object_h25 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h25 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_24)
                )
            )
          let _object_h27 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_27 : Litex.In _value_i2 _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h27 (Litex.sameRefl _value_i2) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_26)
                )
            )
          have h_30 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.NPos (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_member_i8 : Litex.In _value_i8 (Litex.NPos (M := M))) (h_28 : (∃ (_r _s : ℝ), (Litex.denote _value_i7) = M.number (_r : ℂ) ∧ (Litex.denote _value_i8) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i7)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i8)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.NPos (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_member_i8 : Litex.In _value_i8 (Litex.NPos (M := M))) (h_28 : (∃ (_r _s : ℝ), (Litex.denote _value_i7) = M.number (_r : ℂ) ∧ (Litex.denote _value_i8) = M.number (_s : ℂ) ∧ _r ≤ _s)) => (h_2) (Litex.denote _value_i7) _member_i7 (Litex.denote _value_i8) _member_i8 h_28)
                )
            )
          have h_3 : Litex.SequenceNondecreasing _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNondecreasingValue M _known_argument_0)) (Litex.denote _value_i2)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNondecreasingValue M _known_argument_0)) (Litex.denote _value_i1)) := h_2
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNondecreasingValue M _known_argument_0)) (Litex.denote _value_i1)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNondecreasingValue M _known_argument_0)) _known_value)) h_1)) _known_citation
                  )
                )
            )
          have h_35 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_member_i9 : Litex.In _value_i9 (Litex.NPos (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_member_i10 : Litex.In _value_i10 (Litex.NPos (M := M))) (h_33 : (∃ (_r _s : ℝ), (Litex.denote _value_i9) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i9)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.denote _value_i10)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_member_i9 : Litex.In _value_i9 (Litex.NPos (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_member_i10 : Litex.In _value_i10 (Litex.NPos (M := M))) (h_33 : (∃ (_r _s : ℝ), (Litex.denote _value_i9) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r ≤ _s)) => (h_3) (Litex.denote _value_i9) _member_i9 (Litex.denote _value_i10) _member_i10 h_33)
                )
            )
          exact h_3
        )
      )
  )

theorem h_39 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_61 : Litex.In _value_i11 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_63 : Litex.In _value_i12 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_36 : Litex.Same _value_i11 _value_i12) (h_37 : (by
  have _sequence_domain : Litex.In _value_i11 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i11 _value_i11 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_61)
  exact ¬ (Litex.SequenceNondecreasing _value_i11))), ¬ (Litex.SequenceNondecreasing _value_i12) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_61 _Host_i12 _rep_i12 _value_i12 h_63 h_36 h_37
          let _object_h62 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_62 : Litex.In _value_i11 _object_h62 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i11 _value_i11 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h62 (Litex.sameRefl _value_i11) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_61)
                )
            )
          let _object_h64 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_64 : Litex.In _value_i12 _object_h64 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i12 _value_i12 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h64 (Litex.sameRefl _value_i12) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_63)
                )
            )
          have h_38 : ¬ (Litex.SequenceNondecreasing _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNondecreasingValue M _known_argument_0)))) (Litex.denote _value_i12)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNondecreasingValue M _known_argument_0)))) (Litex.denote _value_i11)) := h_37
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNondecreasingValue M _known_argument_0)))) (Litex.denote _value_i11)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNondecreasingValue M _known_argument_0)))) _known_value)) h_36)) _known_citation
                  )
                )
            )
          exact h_38
        )
      )
  )

theorem h_70 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_94 : Litex.In _value_i17 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_96 : Litex.In _value_i18 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_67 : Litex.Same _value_i17 _value_i18) (h_68 : (by
  have _sequence_domain : Litex.In _value_i17 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i17 _value_i17 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_94)
  exact Litex.SequenceNonincreasing _value_i17)), Litex.SequenceNonincreasing _value_i18 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_94 _Host_i18 _rep_i18 _value_i18 h_96 h_67 h_68
          let _object_h95 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_95 : Litex.In _value_i17 _object_h95 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i17 _value_i17 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h95 (Litex.sameRefl _value_i17) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_94)
                )
            )
          let _object_h97 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_97 : Litex.In _value_i18 _object_h97 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i18 _value_i18 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h97 (Litex.sameRefl _value_i18) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_96)
                )
            )
          have h_100 : ∀ {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_member_i23 : Litex.In _value_i23 (Litex.NPos (M := M))) {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.NPos (M := M))) (h_98 : (∃ (_r _s : ℝ), (Litex.denote _value_i23) = M.number (_r : ℂ) ∧ (Litex.denote _value_i24) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i17) (Litex.denote _value_i24)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i17) (Litex.denote _value_i23)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_member_i23 : Litex.In _value_i23 (Litex.NPos (M := M))) {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.NPos (M := M))) (h_98 : (∃ (_r _s : ℝ), (Litex.denote _value_i23) = M.number (_r : ℂ) ∧ (Litex.denote _value_i24) = M.number (_s : ℂ) ∧ _r ≤ _s)) => (h_68) (Litex.denote _value_i23) _member_i23 (Litex.denote _value_i24) _member_i24 h_98)
                )
            )
          have h_69 : Litex.SequenceNonincreasing _value_i18 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNonincreasingValue M _known_argument_0)) (Litex.denote _value_i18)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNonincreasingValue M _known_argument_0)) (Litex.denote _value_i17)) := h_68
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNonincreasingValue M _known_argument_0)) (Litex.denote _value_i17)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceNonincreasingValue M _known_argument_0)) _known_value)) h_67)) _known_citation
                  )
                )
            )
          have h_105 : ∀ {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.NPos (M := M))) {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (_member_i26 : Litex.In _value_i26 (Litex.NPos (M := M))) (h_103 : (∃ (_r _s : ℝ), (Litex.denote _value_i25) = M.number (_r : ℂ) ∧ (Litex.denote _value_i26) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i18) (Litex.denote _value_i26)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i18) (Litex.denote _value_i25)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.NPos (M := M))) {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (_member_i26 : Litex.In _value_i26 (Litex.NPos (M := M))) (h_103 : (∃ (_r _s : ℝ), (Litex.denote _value_i25) = M.number (_r : ℂ) ∧ (Litex.denote _value_i26) = M.number (_s : ℂ) ∧ _r ≤ _s)) => (h_69) (Litex.denote _value_i25) _member_i25 (Litex.denote _value_i26) _member_i26 h_103)
                )
            )
          exact h_69
        )
      )
  )

theorem h_109 : ∀ {_Host_i27 : Type v27} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_135 : Litex.In _value_i27 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i28 : Type v28} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_137 : Litex.In _value_i28 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_106 : Litex.Same _value_i27 _value_i28) (h_107 : (by
  have _sequence_domain : Litex.In _value_i27 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i27 _value_i27 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_135)
  exact ¬ (Litex.SequenceNonincreasing _value_i27))), ¬ (Litex.SequenceNonincreasing _value_i28) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i27 _rep_i27 _value_i27 h_135 _Host_i28 _rep_i28 _value_i28 h_137 h_106 h_107
          let _object_h136 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_136 : Litex.In _value_i27 _object_h136 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i27 _value_i27 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h136 (Litex.sameRefl _value_i27) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_135)
                )
            )
          let _object_h138 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_138 : Litex.In _value_i28 _object_h138 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i28 _value_i28 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h138 (Litex.sameRefl _value_i28) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_137)
                )
            )
          have h_108 : ¬ (Litex.SequenceNonincreasing _value_i28) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNonincreasingValue M _known_argument_0)))) (Litex.denote _value_i28)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNonincreasingValue M _known_argument_0)))) (Litex.denote _value_i27)) := h_107
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNonincreasingValue M _known_argument_0)))) (Litex.denote _value_i27)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceNonincreasingValue M _known_argument_0)))) _known_value)) h_106)) _known_citation
                  )
                )
            )
          exact h_108
        )
      )
  )

theorem h_144 : ∀ {_Host_i33 : Type v33} [_rep_i33 : Litex.Representation M _Host_i33] (_value_i33 : Litex.Obj (M := M) _Host_i33) (h_172 : Litex.In _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i34 : Type v34} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_174 : Litex.In _value_i34 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_141 : Litex.Same _value_i33 _value_i34) (h_142 : (by
  have _sequence_domain : Litex.In _value_i33 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i33 _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_172)
  exact Litex.SequenceStrictlyIncreasing _value_i33)), Litex.SequenceStrictlyIncreasing _value_i34 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i33 _rep_i33 _value_i33 h_172 _Host_i34 _rep_i34 _value_i34 h_174 h_141 h_142
          let _object_h173 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_173 : Litex.In _value_i33 _object_h173 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i33 _value_i33 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h173 (Litex.sameRefl _value_i33) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_172)
                )
            )
          let _object_h175 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_175 : Litex.In _value_i34 _object_h175 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i34 _value_i34 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h175 (Litex.sameRefl _value_i34) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_174)
                )
            )
          have h_178 : ∀ {_Host_i39 : Type _} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (_member_i39 : Litex.In _value_i39 (Litex.NPos (M := M))) {_Host_i40 : Type _} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (_member_i40 : Litex.In _value_i40 (Litex.NPos (M := M))) (h_176 : (∃ (_r _s : ℝ), (Litex.denote _value_i39) = M.number (_r : ℂ) ∧ (Litex.denote _value_i40) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i33) (Litex.denote _value_i39)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i33) (Litex.denote _value_i40)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i39 : Type _} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (_member_i39 : Litex.In _value_i39 (Litex.NPos (M := M))) {_Host_i40 : Type _} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (_member_i40 : Litex.In _value_i40 (Litex.NPos (M := M))) (h_176 : (∃ (_r _s : ℝ), (Litex.denote _value_i39) = M.number (_r : ℂ) ∧ (Litex.denote _value_i40) = M.number (_s : ℂ) ∧ _r < _s)) => (h_142) (Litex.denote _value_i39) _member_i39 (Litex.denote _value_i40) _member_i40 h_176)
                )
            )
          have h_143 : Litex.SequenceStrictlyIncreasing _value_i34 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyIncreasingValue M _known_argument_0)) (Litex.denote _value_i34)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyIncreasingValue M _known_argument_0)) (Litex.denote _value_i33)) := h_142
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyIncreasingValue M _known_argument_0)) (Litex.denote _value_i33)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyIncreasingValue M _known_argument_0)) _known_value)) h_141)) _known_citation
                  )
                )
            )
          have h_183 : ∀ {_Host_i41 : Type _} [_rep_i41 : Litex.Representation M _Host_i41] (_value_i41 : Litex.Obj (M := M) _Host_i41) (_member_i41 : Litex.In _value_i41 (Litex.NPos (M := M))) {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (_member_i42 : Litex.In _value_i42 (Litex.NPos (M := M))) (h_181 : (∃ (_r _s : ℝ), (Litex.denote _value_i41) = M.number (_r : ℂ) ∧ (Litex.denote _value_i42) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i34) (Litex.denote _value_i41)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i34) (Litex.denote _value_i42)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i41 : Type _} [_rep_i41 : Litex.Representation M _Host_i41] (_value_i41 : Litex.Obj (M := M) _Host_i41) (_member_i41 : Litex.In _value_i41 (Litex.NPos (M := M))) {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (_member_i42 : Litex.In _value_i42 (Litex.NPos (M := M))) (h_181 : (∃ (_r _s : ℝ), (Litex.denote _value_i41) = M.number (_r : ℂ) ∧ (Litex.denote _value_i42) = M.number (_s : ℂ) ∧ _r < _s)) => (h_143) (Litex.denote _value_i41) _member_i41 (Litex.denote _value_i42) _member_i42 h_181)
                )
            )
          exact h_143
        )
      )
  )

theorem h_187 : ∀ {_Host_i43 : Type v43} [_rep_i43 : Litex.Representation M _Host_i43] (_value_i43 : Litex.Obj (M := M) _Host_i43) (h_217 : Litex.In _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i44 : Type v44} [_rep_i44 : Litex.Representation M _Host_i44] (_value_i44 : Litex.Obj (M := M) _Host_i44) (h_219 : Litex.In _value_i44 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_184 : Litex.Same _value_i43 _value_i44) (h_185 : (by
  have _sequence_domain : Litex.In _value_i43 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i43 _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_217)
  exact ¬ (Litex.SequenceStrictlyIncreasing _value_i43))), ¬ (Litex.SequenceStrictlyIncreasing _value_i44) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i43 _rep_i43 _value_i43 h_217 _Host_i44 _rep_i44 _value_i44 h_219 h_184 h_185
          let _object_h218 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_218 : Litex.In _value_i43 _object_h218 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i43 _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h218 (Litex.sameRefl _value_i43) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)
                )
            )
          let _object_h220 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_220 : Litex.In _value_i44 _object_h220 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i44 _value_i44 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h220 (Litex.sameRefl _value_i44) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_219)
                )
            )
          have h_186 : ¬ (Litex.SequenceStrictlyIncreasing _value_i44) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyIncreasingValue M _known_argument_0)))) (Litex.denote _value_i44)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyIncreasingValue M _known_argument_0)))) (Litex.denote _value_i43)) := h_185
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyIncreasingValue M _known_argument_0)))) (Litex.denote _value_i43)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyIncreasingValue M _known_argument_0)))) _known_value)) h_184)) _known_citation
                  )
                )
            )
          exact h_186
        )
      )
  )

theorem h_226 : ∀ {_Host_i49 : Type v49} [_rep_i49 : Litex.Representation M _Host_i49] (_value_i49 : Litex.Obj (M := M) _Host_i49) (h_258 : Litex.In _value_i49 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i50 : Type v50} [_rep_i50 : Litex.Representation M _Host_i50] (_value_i50 : Litex.Obj (M := M) _Host_i50) (h_260 : Litex.In _value_i50 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_223 : Litex.Same _value_i49 _value_i50) (h_224 : (by
  have _sequence_domain : Litex.In _value_i49 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i49 _value_i49 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_258)
  exact Litex.SequenceStrictlyDecreasing _value_i49)), Litex.SequenceStrictlyDecreasing _value_i50 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i49 _rep_i49 _value_i49 h_258 _Host_i50 _rep_i50 _value_i50 h_260 h_223 h_224
          let _object_h259 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_259 : Litex.In _value_i49 _object_h259 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i49 _value_i49 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h259 (Litex.sameRefl _value_i49) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_258)
                )
            )
          let _object_h261 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_261 : Litex.In _value_i50 _object_h261 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i50 _value_i50 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h261 (Litex.sameRefl _value_i50) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_260)
                )
            )
          have h_264 : ∀ {_Host_i55 : Type _} [_rep_i55 : Litex.Representation M _Host_i55] (_value_i55 : Litex.Obj (M := M) _Host_i55) (_member_i55 : Litex.In _value_i55 (Litex.NPos (M := M))) {_Host_i56 : Type _} [_rep_i56 : Litex.Representation M _Host_i56] (_value_i56 : Litex.Obj (M := M) _Host_i56) (_member_i56 : Litex.In _value_i56 (Litex.NPos (M := M))) (h_262 : (∃ (_r _s : ℝ), (Litex.denote _value_i55) = M.number (_r : ℂ) ∧ (Litex.denote _value_i56) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i49) (Litex.denote _value_i56)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i49) (Litex.denote _value_i55)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i55 : Type _} [_rep_i55 : Litex.Representation M _Host_i55] (_value_i55 : Litex.Obj (M := M) _Host_i55) (_member_i55 : Litex.In _value_i55 (Litex.NPos (M := M))) {_Host_i56 : Type _} [_rep_i56 : Litex.Representation M _Host_i56] (_value_i56 : Litex.Obj (M := M) _Host_i56) (_member_i56 : Litex.In _value_i56 (Litex.NPos (M := M))) (h_262 : (∃ (_r _s : ℝ), (Litex.denote _value_i55) = M.number (_r : ℂ) ∧ (Litex.denote _value_i56) = M.number (_s : ℂ) ∧ _r < _s)) => (h_224) (Litex.denote _value_i55) _member_i55 (Litex.denote _value_i56) _member_i56 h_262)
                )
            )
          have h_225 : Litex.SequenceStrictlyDecreasing _value_i50 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyDecreasingValue M _known_argument_0)) (Litex.denote _value_i50)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyDecreasingValue M _known_argument_0)) (Litex.denote _value_i49)) := h_224
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyDecreasingValue M _known_argument_0)) (Litex.denote _value_i49)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceStrictlyDecreasingValue M _known_argument_0)) _known_value)) h_223)) _known_citation
                  )
                )
            )
          have h_269 : ∀ {_Host_i57 : Type _} [_rep_i57 : Litex.Representation M _Host_i57] (_value_i57 : Litex.Obj (M := M) _Host_i57) (_member_i57 : Litex.In _value_i57 (Litex.NPos (M := M))) {_Host_i58 : Type _} [_rep_i58 : Litex.Representation M _Host_i58] (_value_i58 : Litex.Obj (M := M) _Host_i58) (_member_i58 : Litex.In _value_i58 (Litex.NPos (M := M))) (h_267 : (∃ (_r _s : ℝ), (Litex.denote _value_i57) = M.number (_r : ℂ) ∧ (Litex.denote _value_i58) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i50) (Litex.denote _value_i58)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i50) (Litex.denote _value_i57)) = M.number (_s : ℂ) ∧ _r < _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i57 : Type _} [_rep_i57 : Litex.Representation M _Host_i57] (_value_i57 : Litex.Obj (M := M) _Host_i57) (_member_i57 : Litex.In _value_i57 (Litex.NPos (M := M))) {_Host_i58 : Type _} [_rep_i58 : Litex.Representation M _Host_i58] (_value_i58 : Litex.Obj (M := M) _Host_i58) (_member_i58 : Litex.In _value_i58 (Litex.NPos (M := M))) (h_267 : (∃ (_r _s : ℝ), (Litex.denote _value_i57) = M.number (_r : ℂ) ∧ (Litex.denote _value_i58) = M.number (_s : ℂ) ∧ _r < _s)) => (h_225) (Litex.denote _value_i57) _member_i57 (Litex.denote _value_i58) _member_i58 h_267)
                )
            )
          exact h_225
        )
      )
  )

theorem h_273 : ∀ {_Host_i59 : Type v59} [_rep_i59 : Litex.Representation M _Host_i59] (_value_i59 : Litex.Obj (M := M) _Host_i59) (h_307 : Litex.In _value_i59 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i60 : Type v60} [_rep_i60 : Litex.Representation M _Host_i60] (_value_i60 : Litex.Obj (M := M) _Host_i60) (h_309 : Litex.In _value_i60 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_270 : Litex.Same _value_i59 _value_i60) (h_271 : (by
  have _sequence_domain : Litex.In _value_i59 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i59 _value_i59 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_307)
  exact ¬ (Litex.SequenceStrictlyDecreasing _value_i59))), ¬ (Litex.SequenceStrictlyDecreasing _value_i60) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i59 _rep_i59 _value_i59 h_307 _Host_i60 _rep_i60 _value_i60 h_309 h_270 h_271
          let _object_h308 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_308 : Litex.In _value_i59 _object_h308 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i59 _value_i59 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h308 (Litex.sameRefl _value_i59) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_307)
                )
            )
          let _object_h310 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_310 : Litex.In _value_i60 _object_h310 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i60 _value_i60 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h310 (Litex.sameRefl _value_i60) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_309)
                )
            )
          have h_272 : ¬ (Litex.SequenceStrictlyDecreasing _value_i60) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyDecreasingValue M _known_argument_0)))) (Litex.denote _value_i60)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyDecreasingValue M _known_argument_0)))) (Litex.denote _value_i59)) := h_271
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyDecreasingValue M _known_argument_0)))) (Litex.denote _value_i59)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceStrictlyDecreasingValue M _known_argument_0)))) _known_value)) h_270)) _known_citation
                  )
                )
            )
          exact h_272
        )
      )
  )

theorem h_316 : ∀ {_Host_i65 : Type v65} [_rep_i65 : Litex.Representation M _Host_i65] (_value_i65 : Litex.Obj (M := M) _Host_i65) (h_352 : Litex.In _value_i65 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i66 : Type v66} [_rep_i66 : Litex.Representation M _Host_i66] (_value_i66 : Litex.Obj (M := M) _Host_i66) (h_354 : Litex.In _value_i66 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_313 : Litex.Same _value_i65 _value_i66) (h_314 : (by
  have _sequence_domain : Litex.In _value_i65 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i65 _value_i65 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_352)
  exact Litex.SequenceBoundedAbove _value_i65)), Litex.SequenceBoundedAbove _value_i66 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i65 _rep_i65 _value_i65 h_352 _Host_i66 _rep_i66 _value_i66 h_354 h_313 h_314
          let _object_h353 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_353 : Litex.In _value_i65 _object_h353 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i65 _value_i65 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h353 (Litex.sameRefl _value_i65) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_352)
                )
            )
          let _object_h355 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_355 : Litex.In _value_i66 _object_h355 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i66 _value_i66 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h355 (Litex.sameRefl _value_i66) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_354)
                )
            )
          have h_356 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i65))) :=
            (by
              litex_checked_step =>
                exact (
                  h_314
                )
            )
          have h_358 : (∃ (_value_i71 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i71) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i65)) (Litex.denote _value_i71))) :=
            (by
              litex_checked_step =>
                exact (
                  h_314
                )
            )
          have h_315 : Litex.SequenceBoundedAbove _value_i66 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedAboveValue M _known_argument_0)) (Litex.denote _value_i66)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedAboveValue M _known_argument_0)) (Litex.denote _value_i65)) := h_314
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedAboveValue M _known_argument_0)) (Litex.denote _value_i65)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedAboveValue M _known_argument_0)) _known_value)) h_313)) _known_citation
                  )
                )
            )
          have h_361 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i66))) :=
            (by
              litex_checked_step =>
                exact (
                  h_315
                )
            )
          have h_363 : (∃ (_value_i72 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i72) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i66)) (Litex.denote _value_i72))) :=
            (by
              litex_checked_step =>
                exact (
                  h_315
                )
            )
          exact h_315
        )
      )
  )

theorem h_367 : ∀ {_Host_i73 : Type v73} [_rep_i73 : Litex.Representation M _Host_i73] (_value_i73 : Litex.Obj (M := M) _Host_i73) (h_405 : Litex.In _value_i73 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i74 : Type v74} [_rep_i74 : Litex.Representation M _Host_i74] (_value_i74 : Litex.Obj (M := M) _Host_i74) (h_407 : Litex.In _value_i74 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_364 : Litex.Same _value_i73 _value_i74) (h_365 : (by
  have _sequence_domain : Litex.In _value_i73 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i73 _value_i73 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_405)
  exact ¬ (Litex.SequenceBoundedAbove _value_i73))), ¬ (Litex.SequenceBoundedAbove _value_i74) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i73 _rep_i73 _value_i73 h_405 _Host_i74 _rep_i74 _value_i74 h_407 h_364 h_365
          let _object_h406 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_406 : Litex.In _value_i73 _object_h406 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i73 _value_i73 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h406 (Litex.sameRefl _value_i73) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_405)
                )
            )
          let _object_h408 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_408 : Litex.In _value_i74 _object_h408 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i74 _value_i74 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h408 (Litex.sameRefl _value_i74) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_407)
                )
            )
          have h_366 : ¬ (Litex.SequenceBoundedAbove _value_i74) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedAboveValue M _known_argument_0)))) (Litex.denote _value_i74)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedAboveValue M _known_argument_0)))) (Litex.denote _value_i73)) := h_365
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedAboveValue M _known_argument_0)))) (Litex.denote _value_i73)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedAboveValue M _known_argument_0)))) _known_value)) h_364)) _known_citation
                  )
                )
            )
          exact h_366
        )
      )
  )

theorem h_414 : ∀ {_Host_i79 : Type v79} [_rep_i79 : Litex.Representation M _Host_i79] (_value_i79 : Litex.Obj (M := M) _Host_i79) (h_454 : Litex.In _value_i79 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i80 : Type v80} [_rep_i80 : Litex.Representation M _Host_i80] (_value_i80 : Litex.Obj (M := M) _Host_i80) (h_456 : Litex.In _value_i80 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_411 : Litex.Same _value_i79 _value_i80) (h_412 : (by
  have _sequence_domain : Litex.In _value_i79 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i79 _value_i79 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_454)
  exact Litex.SequenceBoundedBelow _value_i79)), Litex.SequenceBoundedBelow _value_i80 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i79 _rep_i79 _value_i79 h_454 _Host_i80 _rep_i80 _value_i80 h_456 h_411 h_412
          let _object_h455 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_455 : Litex.In _value_i79 _object_h455 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i79 _value_i79 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h455 (Litex.sameRefl _value_i79) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_454)
                )
            )
          let _object_h457 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_457 : Litex.In _value_i80 _object_h457 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i80 _value_i80 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h457 (Litex.sameRefl _value_i80) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_456)
                )
            )
          have h_458 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i79))) :=
            (by
              litex_checked_step =>
                exact (
                  h_412
                )
            )
          have h_460 : (∃ (_value_i85 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i85) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i79)) (Litex.denote _value_i85))) :=
            (by
              litex_checked_step =>
                exact (
                  h_412
                )
            )
          have h_413 : Litex.SequenceBoundedBelow _value_i80 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedBelowValue M _known_argument_0)) (Litex.denote _value_i80)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedBelowValue M _known_argument_0)) (Litex.denote _value_i79)) := h_412
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedBelowValue M _known_argument_0)) (Litex.denote _value_i79)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedBelowValue M _known_argument_0)) _known_value)) h_411)) _known_citation
                  )
                )
            )
          have h_463 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i80))) :=
            (by
              litex_checked_step =>
                exact (
                  h_413
                )
            )
          have h_465 : (∃ (_value_i86 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i86) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i80)) (Litex.denote _value_i86))) :=
            (by
              litex_checked_step =>
                exact (
                  h_413
                )
            )
          exact h_413
        )
      )
  )

theorem h_469 : ∀ {_Host_i87 : Type v87} [_rep_i87 : Litex.Representation M _Host_i87] (_value_i87 : Litex.Obj (M := M) _Host_i87) (h_511 : Litex.In _value_i87 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i88 : Type v88} [_rep_i88 : Litex.Representation M _Host_i88] (_value_i88 : Litex.Obj (M := M) _Host_i88) (h_513 : Litex.In _value_i88 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_466 : Litex.Same _value_i87 _value_i88) (h_467 : (by
  have _sequence_domain : Litex.In _value_i87 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i87 _value_i87 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_511)
  exact ¬ (Litex.SequenceBoundedBelow _value_i87))), ¬ (Litex.SequenceBoundedBelow _value_i88) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i87 _rep_i87 _value_i87 h_511 _Host_i88 _rep_i88 _value_i88 h_513 h_466 h_467
          let _object_h512 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_512 : Litex.In _value_i87 _object_h512 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i87 _value_i87 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h512 (Litex.sameRefl _value_i87) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_511)
                )
            )
          let _object_h514 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_514 : Litex.In _value_i88 _object_h514 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i88 _value_i88 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h514 (Litex.sameRefl _value_i88) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_513)
                )
            )
          have h_468 : ¬ (Litex.SequenceBoundedBelow _value_i88) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedBelowValue M _known_argument_0)))) (Litex.denote _value_i88)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedBelowValue M _known_argument_0)))) (Litex.denote _value_i87)) := h_467
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedBelowValue M _known_argument_0)))) (Litex.denote _value_i87)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedBelowValue M _known_argument_0)))) _known_value)) h_466)) _known_citation
                  )
                )
            )
          exact h_468
        )
      )
  )

theorem h_520 : ∀ {_Host_i93 : Type v93} [_rep_i93 : Litex.Representation M _Host_i93] (_value_i93 : Litex.Obj (M := M) _Host_i93) (h_564 : Litex.In _value_i93 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i94 : Type v94} [_rep_i94 : Litex.Representation M _Host_i94] (_value_i94 : Litex.Obj (M := M) _Host_i94) (h_566 : Litex.In _value_i94 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_517 : Litex.Same _value_i93 _value_i94) (h_518 : (by
  have _sequence_domain : Litex.In _value_i93 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i93 _value_i93 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_564)
  exact Litex.SequenceBounded _value_i93)), Litex.SequenceBounded _value_i94 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i93 _rep_i93 _value_i93 h_564 _Host_i94 _rep_i94 _value_i94 h_566 h_517 h_518
          let _object_h565 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_565 : Litex.In _value_i93 _object_h565 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i93 _value_i93 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h565 (Litex.sameRefl _value_i93) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_564)
                )
            )
          let _object_h567 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_567 : Litex.In _value_i94 _object_h567 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i94 _value_i94 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h567 (Litex.sameRefl _value_i94) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_566)
                )
            )
          have h_568 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i93))) :=
            (by
              litex_checked_step =>
                exact (
                  h_518
                )
            )
          have h_570 : (∃ (_value_i99 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i99) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i93)) (Litex.denote _value_i99))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_518).1
                )
            )
          have h_572 : (∃ (_value_i100 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i100) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i93)) (Litex.denote _value_i100))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_518).2
                )
            )
          have h_573 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i93)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_518).2
                )
            )
          have h_574 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i93)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_518).1
                )
            )
          have h_519 : Litex.SequenceBounded _value_i94 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedValue M _known_argument_0)) (Litex.denote _value_i94)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedValue M _known_argument_0)) (Litex.denote _value_i93)) := h_518
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedValue M _known_argument_0)) (Litex.denote _value_i93)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceBoundedValue M _known_argument_0)) _known_value)) h_517)) _known_citation
                  )
                )
            )
          have h_577 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i94))) :=
            (by
              litex_checked_step =>
                exact (
                  h_519
                )
            )
          have h_579 : (∃ (_value_i101 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i101) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i94)) (Litex.denote _value_i101))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_519).1
                )
            )
          have h_581 : (∃ (_value_i102 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i102) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i94)) (Litex.denote _value_i102))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_519).2
                )
            )
          have h_582 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i94)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_519).2
                )
            )
          have h_583 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i94)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_519).1
                )
            )
          exact h_519
        )
      )
  )

theorem h_587 : ∀ {_Host_i103 : Type v103} [_rep_i103 : Litex.Representation M _Host_i103] (_value_i103 : Litex.Obj (M := M) _Host_i103) (h_633 : Litex.In _value_i103 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i104 : Type v104} [_rep_i104 : Litex.Representation M _Host_i104] (_value_i104 : Litex.Obj (M := M) _Host_i104) (h_635 : Litex.In _value_i104 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_584 : Litex.Same _value_i103 _value_i104) (h_585 : (by
  have _sequence_domain : Litex.In _value_i103 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i103 _value_i103 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_633)
  exact ¬ (Litex.SequenceBounded _value_i103))), ¬ (Litex.SequenceBounded _value_i104) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i103 _rep_i103 _value_i103 h_633 _Host_i104 _rep_i104 _value_i104 h_635 h_584 h_585
          let _object_h634 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_634 : Litex.In _value_i103 _object_h634 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i103 _value_i103 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h634 (Litex.sameRefl _value_i103) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_633)
                )
            )
          let _object_h636 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_636 : Litex.In _value_i104 _object_h636 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i104 _value_i104 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h636 (Litex.sameRefl _value_i104) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_635)
                )
            )
          have h_586 : ¬ (Litex.SequenceBounded _value_i104) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedValue M _known_argument_0)))) (Litex.denote _value_i104)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedValue M _known_argument_0)))) (Litex.denote _value_i103)) := h_585
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedValue M _known_argument_0)))) (Litex.denote _value_i103)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceBoundedValue M _known_argument_0)))) _known_value)) h_584)) _known_citation
                  )
                )
            )
          exact h_586
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_property_x5f_citations_x2f_statement_x2e_lit
