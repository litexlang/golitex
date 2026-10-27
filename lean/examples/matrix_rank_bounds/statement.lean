import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)), (((by
  let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21))
  exact Litex.Le _atomic_wd_1_0 _value_i1)) ∧ ((by
  let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21))
  exact Litex.Le _atomic_wd_1_0 _value_i2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_21
          have h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_4)
                )
            )
          have h_7 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_6)
                )
            )
          let _object_h22 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)))
          have h_22 : Litex.In _value_i3 _object_h22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6) _object_h22 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6))) h_21)
                )
            )
          have h_195 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_197 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_212 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_196 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_195)
                )
            )
          have h_198 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_197)
                )
            )
          let _object_h213 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)))
          have h_213 : Litex.In _value_i3 _object_h213 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197) _object_h213 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197))) h_212)
                )
            )
          have h_217 : Litex.In (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
            exact h_212)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_214 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_195
                          )
                      )
                    have h_224 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_214)
                          )
                      )
                    have h_215 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_197
                          )
                      )
                    have h_233 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_215)
                          )
                      )
                    have h_216 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                              exact h_212)
                          )
                      )
                    let _object_h246 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)))
                    have h_246 : Litex.In _value_i3 _object_h246 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197) _object_h246 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197))) h_216)
                          )
                      )
                    exact (And.left (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankInN _rank
                  ) (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i1) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeRows _rank
                  ) (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i2) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeCols _rank
                  ))))
                  )
                )
            )

          have h_551 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
            exact h_212)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_212)) h_217)
                )
            )

          have h_218 : Litex.Le (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
            exact h_212)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_214 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_195
                          )
                      )
                    have h_224 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_214)
                          )
                      )
                    have h_215 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_197
                          )
                      )
                    have h_233 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_215)
                          )
                      )
                    have h_216 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                              exact h_212)
                          )
                      )
                    let _object_h246 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)))
                    have h_246 : Litex.In _value_i3 _object_h246 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197) _object_h246 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197))) h_216)
                          )
                      )
                    exact (And.left (And.right (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankInN _rank
                  ) (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i1) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeRows _rank
                  ) (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i2) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeCols _rank
                  )))))
                  )
                )
            )

          have h_219 : Litex.Le (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
            exact h_212)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_214 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_195
                          )
                      )
                    have h_224 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_214)
                          )
                      )
                    have h_215 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_197
                          )
                      )
                    have h_233 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_215)
                          )
                      )
                    have h_216 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                              exact h_212)
                          )
                      )
                    let _object_h246 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)))
                    have h_246 : Litex.In _value_i3 _object_h246 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197) _object_h246 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197))) h_216)
                          )
                      )
                    exact (And.right (And.right (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankInN _rank
                  ) (And.intro (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i1) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeRows _rank
                  ) (show (by
                    let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                      exact h_216))
                    exact Litex.Le _atomic_wd_1_0 _value_i2) from by
                    let _rank := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_214 h_215 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
                    exact h_216))
                    exact Litex.matrixRankLeCols _rank
                  )))))
                  )
                )
            )
          exact (And.intro (by
            let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
              exact h_212))
            exact h_218) (by
            let _atomic_wd_1_0 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_195 h_197 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_195 h_197)
              exact h_212))
            exact h_219))
        )
      )
  )

theorem h_885 : (by
  have h_886 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  have h_887 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
        )
    )
  have h_888 : (by
    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887)
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
        )
    )
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
    (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_886 h_887 (by
      let _atomic_wd_1_0 := _wd_1_0
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
      exact h_888)))
    exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_886 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_891 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_886)
                )
            )
          have h_887 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
                )
            )
          have h_894 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (3 : ℂ)) h_887)
                )
            )
          have h_888 : (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887)
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
                )
            )
          let _object_h928 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)))
          have h_928 : Litex.In (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887) _object_h928 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887) (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887) (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887) _object_h928 (Litex.sameRefl (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887)) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887))) h_888)
                )
            )
          have h_889 : Litex.Le (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_886 h_887 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
            exact h_888))) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.left ((h_3 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_886 (Litex.number (M := M) (3 : ℂ)) h_887 (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887) h_888))
                )
            )
          have h_890 : Litex.Le (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_886 h_887 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
            exact h_888))) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.right ((h_3 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_886 (Litex.number (M := M) (3 : ℂ)) h_887 (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887) h_888))
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) h_886 h_887);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.matrixRank _wd_1_0 _wd_1_1 _wd_1_2 h_886 h_887 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_886 h_887)
            exact h_888)))
          exact h_889)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_bounds_x2f_statement_x2e_lit
