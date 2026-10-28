import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_log_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.RPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.RPos (M := M))) (h_1 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) _value_i1) (h_2 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) _value_i2), (by
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
  exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.log _value_i1 _value_i2 (Litex.inRPos_real _value_i1 h_6) (Litex.inRPos_real _value_i2 h_10) h_7 h_11 (fun _litex_same => h_1 _litex_same.symm))
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
          have h_152 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_156 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_153 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_152)
                )
            )
          have h_154 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_153)
                )
            )
          have h_155 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_153) _litex_zero.symm)
                )
            )
          have h_157 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_156)
                )
            )
          have h_158 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_157)
                )
            )
          have h_159 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_157) _litex_zero.symm)
                )
            )
          let _object_w7 := (Litex.log _value_i1 _value_i2 (Litex.inRPos_real _value_i1 h_152) (Litex.inRPos_real _value_i2 h_156) h_153 h_157 (fun _litex_same => h_1 _litex_same.symm))

          have h_5 : (by
            let _atomic_wd_1_1 := _object_w7
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w7
                    exact (let _log_base := (And.intro h_153 (show ¬ Litex.Same _value_i1 (Litex.number 1) from fun _log_eq => h_1 _log_eq.symm)); let _log_arg := (And.intro h_157 (show ¬ Litex.Same _value_i2 (Litex.number 1) from fun _log_eq => h_2 _log_eq.symm)); fun _litex_equal => (Litex.logNonzeroOfGuards _atomic_wd_1_1 _log_base.1 _log_base.2 _log_arg.1 _log_arg.2) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w7
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_log_x5f_nonzero_x5f_reversed_x2f_statement_x2e_lit
