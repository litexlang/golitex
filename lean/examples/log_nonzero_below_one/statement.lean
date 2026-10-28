import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_log_x5f_nonzero_x5f_below_x5f_one_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.RPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.RPos (M := M))) (h_1 : Litex.Lt _value_i1 (Litex.number (M := M) (1 : ℂ))) (h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (1 : ℂ))), (by
  have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i1 h_6)
        )
    )
  have h_11 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_10)
        )
    )
  exact ¬ Litex.Same (Litex.log _value_i1 _value_i2 (Litex.inRPos_real _value_i1 h_6) (Litex.inRPos_real _value_i2 h_10) h_7 h_11 (Litex.ltNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) h_1)) (Litex.number (M := M) (0 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_10 h_1 h_2
          have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_6)
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_7)
                )
            )
          have h_9 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_7) _litex_zero.symm)
                )
            )
          have h_11 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_10)
                )
            )
          have h_12 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_11)
                )
            )
          have h_13 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_11) _litex_zero.symm)
                )
            )
          have h_44 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.number (M := M) (1 : ℂ)) h_8 h_1)
                )
            )
          have h_81 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (1 : ℂ)) h_12 h_2)
                )
            )
          have h_197 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_201 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_198 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_197)
                )
            )
          have h_199 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_198)
                )
            )
          have h_200 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_198) _litex_zero.symm)
                )
            )
          have h_202 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_201)
                )
            )
          have h_203 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_202)
                )
            )
          have h_204 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_202) _litex_zero.symm)
                )
            )
          have h_235 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.number (M := M) (1 : ℂ)) h_199 h_1)
                )
            )
          have h_272 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (1 : ℂ)) h_203 h_2)
                )
            )
          let _object_w7 := (Litex.log _value_i1 _value_i2 (Litex.inRPos_real _value_i1 h_197) (Litex.inRPos_real _value_i2 h_201) h_198 h_202 (Litex.ltNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) h_1))

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w7
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (let _log_base := (And.intro h_198 (Litex.ltNotSame _value_i1 (Litex.number 1) h_1)); let _log_arg := (And.intro h_202 (Litex.ltNotSame _value_i2 (Litex.number 1) h_2)); fun _litex_equal => (Litex.logNonzeroOfGuards _atomic_wd_1_0 _log_base.1 _log_base.2 _log_arg.1 _log_arg.2) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w7
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_log_x5f_nonzero_x5f_below_x5f_one_x2f_statement_x2e_lit
