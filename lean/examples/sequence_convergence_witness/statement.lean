import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_convergence_x5f_witness_x2f_statement_x2e_lit

universe u v1 v2 v30 v38 v39
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_11 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_9)
  have _sequence_limit_real : Litex.In _value_i2 (Litex.R (M := M)) := h_11
  exact Litex.HasSequenceLimit _value_i1 _value_i2)), (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_9)
  exact Litex.SequenceConvergent _value_i1) :=
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
          have h_18 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_20 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          let _object_h19 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_19 : Litex.In _value_i1 _object_h19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h19 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_18)
                )
            )
          have h_5 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_26 : Litex.In _value_i3 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)
                    have h_41 : Litex.In _value_i3 (Litex.R (M := M)) := h_20
                    have h_42 : Litex.Same _value_i3 _value_i2 := rfl
                    have h_6 : Litex.HasSequenceLimit _value_i1 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_47 : Litex.HasSequenceLimit _value_i1 _value_i2 := h_6
                    exact ⟨_value_i3, h_41, h_47⟩
                )
            )
          have h_7 : (by
            have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_18)
            exact Litex.SequenceConvergent _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_18)
                    exact (show ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_54 : Litex.In _value_i17 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i1 _value_i17 from h_5))
                )
            )

          have h_61 : (∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i24) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i1) (Litex.denote _value_i24))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          exact h_7
        )
      )
  )

theorem h_76 : ∀ {_Host_i30 : Type v30} [_rep_i30 : Litex.Representation M _Host_i30] (_value_i30 : Litex.Obj (M := M) _Host_i30) (h_96 : Litex.In _value_i30 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_73 : (by
  have _sequence_domain : Litex.In _value_i30 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i30 _value_i30 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_96)
  exact Litex.SequenceConvergent _value_i30)), ∃ (_value_i31 : Litex.Obj (M := M) M.Value), ∃ (h_100 : Litex.In _value_i31 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i30 _value_i31 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i30 _rep_i30 _value_i30 h_96 h_73
          let _object_h97 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_97 : Litex.In _value_i30 _object_h97 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i30 _value_i30 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h97 (Litex.sameRefl _value_i30) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_96)
                )
            )
          have h_99 : (∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i35) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i30) (Litex.denote _value_i35))) :=
            (by
              litex_checked_step =>
                exact (
                  h_73
                )
            )
          have h_75 : ∃ (_value_i31 : Litex.Obj (M := M) M.Value), ∃ (h_100 : Litex.In _value_i31 (Litex.R (M := M))), Litex.HasSequenceLimit _value_i30 _value_i31 :=
            (by
              litex_checked_step =>
                exact (
                  h_99
                )
            )
          exact h_75
        )
      )
  )

theorem h_106 : ∀ {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_109 : Litex.In _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i39 : Type v39} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (h_111 : Litex.In _value_i39 (Litex.R (M := M))) (h_104 : (by
  have _sequence_domain : Litex.In _value_i38 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_109)
  have _sequence_limit_real : Litex.In _value_i39 (Litex.R (M := M)) := h_111
  exact Litex.HasSequenceLimit _value_i38 _value_i39)), (by
  have _sequence_domain : Litex.In _value_i38 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_109)
  exact Litex.SequenceConvergent _value_i38) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i38 _rep_i38 _value_i38 h_109 _Host_i39 _rep_i39 _value_i39 h_111 h_104
          let _object_h110 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_110 : Litex.In _value_i38 _object_h110 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h110 (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_109)
                )
            )
          have h_118 : Litex.In _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_109
                )
            )
          have h_120 : Litex.In _value_i39 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_111
                )
            )
          let _object_h119 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_119 : Litex.In _value_i38 _object_h119 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h119 (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_118)
                )
            )
          have h_107 : Litex.SequenceConvergent _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_126 : (by
                      let _atomic_wd_1_1 := (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
                      exact Litex.In _value_i38 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))
                              exact h_118)
                          )
                      )
                    let _object_h134 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
                    have h_134 : Litex.In _value_i38 _object_h134 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h134 (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_126)
                          )
                      )
                    have h_127 : Litex.In _value_i39 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_120
                          )
                      )
                    have h_128 : Litex.HasSequenceLimit _value_i38 _value_i39 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_104
                          )
                      )
                    have h_129 : Litex.SequenceConvergent _value_i38 :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((h_3 (M := M)) _value_i38 h_126 _value_i39 h_127 h_128)
                          )
                      )
                    have h_152 : (∃ (_value_i53 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i53) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i38) (Litex.denote _value_i53))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_129
                          )
                      )
                    exact h_129
                  )
                )
            )

          have h_155 : (∃ (_value_i56 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i56) (M.standard Litex.StandardSetValue.real)), (Litex.HasSequenceLimitValue M (Litex.denote _value_i38) (Litex.denote _value_i56))) :=
            (by
              litex_checked_step =>
                exact (
                  h_107
                )
            )
          exact h_107
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_convergence_x5f_witness_x2f_statement_x2e_lit
