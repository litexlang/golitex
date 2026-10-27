import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_infimum_x5f_candidate_x2f_statement_x2e_lit

universe u v1 v2 v7 v8 v14 v15 v16
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))) (h_2 : (Litex.RealGreatestLowerBound _value_i1 _value_i2)), (by
  let _equal_wd_1_0 := (Litex.infimum _value_i1 h_1 (Litex.realInfimumExistsOfCertificate _value_i1 _value_i2 h_2))
  exact Litex.Same _equal_wd_1_0 _value_i2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1 h_2
          have h_22 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_23 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          exact (Eq.trans (Litex.infimumValue_eq_certificate _value_i1 _value_i2 h_2) (show @Eq M.Value _ _ from Eq.refl _))
        )
      )
  )

theorem h_65 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_67 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_68 : Litex.In _value_i8 (Litex.R (M := M))) (h_62 : Litex.Subset _value_i7 (Litex.R (M := M))) (h_63 : (Litex.RealGreatestLowerBound _value_i7 _value_i8)), (by
  let _equal_wd_1_1 := (Litex.infimum _value_i7 h_62 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_63))
  exact Litex.Same _value_i8 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_67 _Host_i8 _rep_i8 _value_i8 h_68 h_62 h_63
          have h_84 : Litex.IsSet _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  h_67
                )
            )
          have h_85 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_68
                )
            )
          have h_66 : (by
            have h_91 : Litex.Subset _value_i7 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_62
                  )
              )
            have h_92 : (Litex.RealGreatestLowerBound _value_i7 _value_i8) :=
              (by
                litex_checked_step =>
                  exact (
                    h_63
                  )
              )
            exact (by
              let _equal_wd_1_0 := (Litex.infimum _value_i7 h_91 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_92))
              exact Litex.Same _equal_wd_1_0 _value_i8)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_89 : Litex.IsSet _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_84
                          )
                      )
                    have h_90 : Litex.In _value_i8 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_85
                          )
                      )
                    have h_91 : Litex.Subset _value_i7 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_62
                          )
                      )
                    have h_92 : (Litex.RealGreatestLowerBound _value_i7 _value_i8) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_63
                          )
                      )
                    have h_93 : Litex.Same (Litex.infimum _value_i7 h_91 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_92)) _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((h_4 (M := M)) _value_i7 h_89 _value_i8 h_90 h_91 h_92)
                          )
                      )
                    exact (let _equal_wd_1_0 := (Litex.infimum _value_i7 h_91 (Litex.realInfimumExistsOfCertificate _value_i7 _value_i8 h_92));
                  (show Litex.Same _equal_wd_1_0 _value_i8 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_93).trans (Litex.sameRefl _value_i8)))))
                  )
                )
            )
          exact (h_66).symm
        )
      )
  )

theorem h_157 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_158 : Litex.IsSet _value_i14) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_159 : Litex.IsSet _value_i15) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_160 : Litex.In _value_i16 (Litex.R (M := M))) (h_153 : Litex.Same _value_i14 _value_i15) (h_154 : Litex.Subset _value_i14 (Litex.R (M := M))) (h_155 : (Litex.RealGreatestLowerBound _value_i14 _value_i16)), (by
  let _equal_wd_1_0 := (Litex.infimum _value_i14 h_154 (Litex.realInfimumExistsOfCertificate _value_i14 _value_i16 h_155))
  let _equal_wd_1_1 := (Litex.infimum _value_i15 (Litex.subsetOfSame _value_i14 (Litex.R (M := M)) _value_i15 (Litex.R (M := M)) h_153 (show @Eq M.Value _ _ from Eq.refl _) h_154) (Litex.realInfimumExistsOfCertificate _value_i15 _value_i16 (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i15) (Litex.denote _value_i16)) from by
    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i14) (Litex.denote _value_i16)) := h_155
    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i14) (Litex.denote _value_i16)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote _value_i16))) h_153))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i15) _known_value)) (show @Eq M.Value _ _ from Eq.refl _))) _known_citation
  )))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_158 _Host_i15 _rep_i15 _value_i15 h_159 _Host_i16 _rep_i16 _value_i16 h_160 h_153 h_154 h_155
          have h_188 : Litex.IsSet _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  h_158
                )
            )
          have h_189 : Litex.IsSet _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  h_159
                )
            )
          have h_190 : Litex.In _value_i16 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_160
                )
            )
          exact (congrArg (Litex.infimumValue (M := M)) h_153)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_infimum_x5f_candidate_x2f_statement_x2e_lit
