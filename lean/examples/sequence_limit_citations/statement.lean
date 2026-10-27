import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_citations_x2f_statement_x2e_lit

universe u v1 v2 v15 v16 v21 v22 v29 v30 v35 v36 v37 v38 v43 v44 v45 v46
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_24 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_1 : Litex.Same _value_i1 _value_i2) (h_2 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_24)
  exact Litex.SequenceCauchy _value_i1)), Litex.SequenceCauchy _value_i2 :=
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
          have h_32 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.RPos (M := M))), (∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i8) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i9 : M.Value) => ∃ (_ : M.mem _raw_i9 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ _raw_i9 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i9 : M.Value) => ∃ (_ : M.mem _raw_i9 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ _raw_i9 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i10 : M.Value) => ∃ (_ : M.mem _raw_i10 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_member_i7 : Litex.In _value_i7 (Litex.RPos (M := M))) => (h_2) (Litex.denote _value_i7) _member_i7)
                )
            )
          have h_3 : Litex.SequenceCauchy _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceCauchyValue M _known_argument_0)) (Litex.denote _value_i2)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceCauchyValue M _known_argument_0)) (Litex.denote _value_i1)) := h_2
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceCauchyValue M _known_argument_0)) (Litex.denote _value_i1)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceCauchyValue M _known_argument_0)) _known_value)) h_1)) _known_citation
                  )
                )
            )
          have h_39 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_member_i11 : Litex.In _value_i11 (Litex.RPos (M := M))), (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i12) (Litex.denote (Litex.NPos (M := M)))), (∀ _member : M.Value, M.mem _member (Litex.FiniteFunction.cartValue (M := M) ![(Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i13 : M.Value) => ∃ (_ : M.mem _raw_i13 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i12) = M.number (_r : ℂ) ∧ _raw_i13 = M.number (_s : ℂ) ∧ _r ≤ _s))), (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.NPos (M := M))) (fun (_raw_i13 : M.Value) => ∃ (_ : M.mem _raw_i13 (Litex.denote (Litex.NPos (M := M)))), (∃ (_r _s : ℝ), (Litex.denote _value_i12) = M.number (_r : ℂ) ∧ _raw_i13 = M.number (_s : ℂ) ∧ _r ≤ _s)))]) → M.mem _member (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (fun (_raw_i14 : M.Value) => ∃ (_ : M.mem _raw_i14 (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.NPos (M := M))), (Litex.denote (Litex.NPos (M := M)))])), (∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FunctionSemantics.callValue (M := M) _raw_i14 (M.number (1 : ℂ)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FunctionSemantics.callValue (M := M) _raw_i14 (M.number (2 : ℂ)))))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i11) = M.number (_s : ℂ) ∧ _r < _s))))) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_member_i11 : Litex.In _value_i11 (Litex.RPos (M := M))) => (h_3) (Litex.denote _value_i11) _member_i11)
                )
            )
          exact h_3
        )
      )
  )

theorem h_43 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_65 : Litex.In _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_67 : Litex.In _value_i16 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_40 : Litex.Same _value_i15 _value_i16) (h_41 : (by
  have _sequence_domain : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_65)
  exact ¬ (Litex.SequenceCauchy _value_i15))), ¬ (Litex.SequenceCauchy _value_i16) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_65 _Host_i16 _rep_i16 _value_i16 h_67 h_40 h_41
          let _object_h66 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_66 : Litex.In _value_i15 _object_h66 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h66 (Litex.sameRefl _value_i15) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_65)
                )
            )
          let _object_h68 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_68 : Litex.In _value_i16 _object_h68 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i16 _value_i16 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h68 (Litex.sameRefl _value_i16) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_67)
                )
            )
          have h_42 : ¬ (Litex.SequenceCauchy _value_i16) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceCauchyValue M _known_argument_0)))) (Litex.denote _value_i16)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceCauchyValue M _known_argument_0)))) (Litex.denote _value_i15)) := h_41
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceCauchyValue M _known_argument_0)))) (Litex.denote _value_i15)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceCauchyValue M _known_argument_0)))) _known_value)) h_40)) _known_citation
                  )
                )
            )
          exact h_42
        )
      )
  )

theorem h_74 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_98 : Litex.In _value_i21 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_100 : Litex.In _value_i22 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_71 : Litex.Same _value_i21 _value_i22) (h_72 : (by
  have _sequence_domain : Litex.In _value_i21 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i21 _value_i21 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_98)
  exact Litex.SequenceConvergent _value_i21)), Litex.SequenceConvergent _value_i22 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_98 _Host_i22 _rep_i22 _value_i22 h_100 h_71 h_72
          let _object_h99 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_99 : Litex.In _value_i21 _object_h99 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i21 _value_i21 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h99 (Litex.sameRefl _value_i21) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_98)
                )
            )
          let _object_h101 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_101 : Litex.In _value_i22 _object_h101 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i22 _value_i22 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h101 (Litex.sameRefl _value_i22) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_100)
                )
            )
          have h_103 : (∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i27) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i21) (Litex.denote _value_i27))) :=
            (by
              litex_checked_step =>
                exact (
                  h_72
                )
            )
          have h_73 : Litex.SequenceConvergent _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.SequenceConvergentValue M _known_argument_0)) (Litex.denote _value_i22)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.SequenceConvergentValue M _known_argument_0)) (Litex.denote _value_i21)) := h_72
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.SequenceConvergentValue M _known_argument_0)) (Litex.denote _value_i21)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.SequenceConvergentValue M _known_argument_0)) _known_value)) h_71)) _known_citation
                  )
                )
            )
          have h_107 : (∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i28) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i22) (Litex.denote _value_i28))) :=
            (by
              litex_checked_step =>
                exact (
                  h_73
                )
            )
          exact h_73
        )
      )
  )

theorem h_111 : ∀ {_Host_i29 : Type v29} [_rep_i29 : Litex.Representation M _Host_i29] (_value_i29 : Litex.Obj (M := M) _Host_i29) (h_137 : Litex.In _value_i29 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i30 : Type v30} [_rep_i30 : Litex.Representation M _Host_i30] (_value_i30 : Litex.Obj (M := M) _Host_i30) (h_139 : Litex.In _value_i30 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_108 : Litex.Same _value_i29 _value_i30) (h_109 : (by
  have _sequence_domain : Litex.In _value_i29 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i29 _value_i29 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_137)
  exact ¬ (Litex.SequenceConvergent _value_i29))), ¬ (Litex.SequenceConvergent _value_i30) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i29 _rep_i29 _value_i29 h_137 _Host_i30 _rep_i30 _value_i30 h_139 h_108 h_109
          let _object_h138 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_138 : Litex.In _value_i29 _object_h138 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i29 _value_i29 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h138 (Litex.sameRefl _value_i29) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_137)
                )
            )
          let _object_h140 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_140 : Litex.In _value_i30 _object_h140 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i30 _value_i30 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h140 (Litex.sameRefl _value_i30) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_139)
                )
            )
          have h_110 : ¬ (Litex.SequenceConvergent _value_i30) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceConvergentValue M _known_argument_0)))) (Litex.denote _value_i30)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceConvergentValue M _known_argument_0)))) (Litex.denote _value_i29)) := h_109
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceConvergentValue M _known_argument_0)))) (Litex.denote _value_i29)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (¬ ((Litex.SequenceConvergentValue M _known_argument_0)))) _known_value)) h_108)) _known_citation
                  )
                )
            )
          exact h_110
        )
      )
  )

theorem h_147 : ∀ {_Host_i35 : Type v35} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_179 : Litex.In _value_i35 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i36 : Type v36} [_rep_i36 : Litex.Representation M _Host_i36] (_value_i36 : Litex.Obj (M := M) _Host_i36) (h_181 : Litex.In _value_i36 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i37 : Type v37} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (h_183 : Litex.In _value_i37 (Litex.R (M := M))) {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_184 : Litex.In _value_i38 (Litex.R (M := M))) (h_143 : Litex.Same _value_i35 _value_i36) (h_144 : Litex.Same _value_i37 _value_i38) (h_145 : (by
  have _sequence_domain : Litex.In _value_i35 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i35 _value_i35 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_179)
  have _sequence_limit_real : Litex.In _value_i37 (Litex.R (M := M)) := h_183
  exact Litex.HasSequenceLimit _value_i35 _value_i37)), Litex.HasSequenceLimit _value_i36 _value_i38 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i35 _rep_i35 _value_i35 h_179 _Host_i36 _rep_i36 _value_i36 h_181 _Host_i37 _rep_i37 _value_i37 h_183 _Host_i38 _rep_i38 _value_i38 h_184 h_143 h_144 h_145
          let _object_h180 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_180 : Litex.In _value_i35 _object_h180 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i35 _value_i35 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h180 (Litex.sameRefl _value_i35) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_179)
                )
            )
          let _object_h182 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_182 : Litex.In _value_i36 _object_h182 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i36 _value_i36 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h182 (Litex.sameRefl _value_i36) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_181)
                )
            )
          have h_146 : Litex.HasSequenceLimit _value_i36 _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i36) (Litex.denote _value_i38)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i35) (Litex.denote _value_i37)) := h_145
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i35) (Litex.denote _value_i37)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote _value_i37))) h_143))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i36) _known_value)) h_144)) _known_citation
                  )
                )
            )
          exact h_146
        )
      )
  )

theorem h_200 : ∀ {_Host_i43 : Type v43} [_rep_i43 : Litex.Representation M _Host_i43] (_value_i43 : Litex.Obj (M := M) _Host_i43) (h_235 : Litex.In _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i44 : Type v44} [_rep_i44 : Litex.Representation M _Host_i44] (_value_i44 : Litex.Obj (M := M) _Host_i44) (h_237 : Litex.In _value_i44 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i45 : Type v45} [_rep_i45 : Litex.Representation M _Host_i45] (_value_i45 : Litex.Obj (M := M) _Host_i45) (h_239 : Litex.In _value_i45 (Litex.R (M := M))) {_Host_i46 : Type v46} [_rep_i46 : Litex.Representation M _Host_i46] (_value_i46 : Litex.Obj (M := M) _Host_i46) (h_240 : Litex.In _value_i46 (Litex.R (M := M))) (h_196 : Litex.Same _value_i43 _value_i44) (h_197 : Litex.Same _value_i45 _value_i46) (h_198 : (by
  have _sequence_domain : Litex.In _value_i43 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i43 _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_235)
  have _sequence_limit_real : Litex.In _value_i45 (Litex.R (M := M)) := h_239
  exact ¬ (Litex.HasSequenceLimit _value_i43 _value_i45))), ¬ (Litex.HasSequenceLimit _value_i44 _value_i46) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i43 _rep_i43 _value_i43 h_235 _Host_i44 _rep_i44 _value_i44 h_237 _Host_i45 _rep_i45 _value_i45 h_239 _Host_i46 _rep_i46 _value_i46 h_240 h_196 h_197 h_198
          let _object_h236 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_236 : Litex.In _value_i43 _object_h236 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i43 _value_i43 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h236 (Litex.sameRefl _value_i43) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_235)
                )
            )
          let _object_h238 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_238 : Litex.In _value_i44 _object_h238 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i44 _value_i44 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h238 (Litex.sameRefl _value_i44) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_237)
                )
            )
          have h_199 : ¬ (Litex.HasSequenceLimit _value_i44 _value_i46) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)))) (Litex.denote _value_i44) (Litex.denote _value_i46)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)))) (Litex.denote _value_i43) (Litex.denote _value_i45)) := h_198
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)))) (Litex.denote _value_i43) (Litex.denote _value_i45)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)))) _known_value (Litex.denote _value_i45))) h_196))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((Litex.HasSequenceLimitValue M _known_argument_0 _known_argument_1)))) (Litex.denote _value_i44) _known_value)) h_197)) _known_citation
                  )
                )
            )
          exact h_199
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_citations_x2f_statement_x2e_lit
