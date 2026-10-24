import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_refined_x5f_numeric_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.Q (M := M))) (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), Litex.In _value_i1 (Litex.QPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          have h_2 : Litex.In _value_i1 (Litex.QPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_intro _value_i1 h_16 h_1)
                )
            )
          have h_68 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_positive _value_i1 h_2)
                )
            )
          have h_69 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_68)
                )
            )
          have h_70 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_68) _litex_zero.symm)
                )
            )
          exact h_2
        )
      )
  )

theorem h_73 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_87 : Litex.In _value_i2 (Litex.Q (M := M))) (h_71 : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i2 (Litex.QNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_87 h_71
          have h_72 : Litex.In _value_i2 (Litex.QNeg (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_intro _value_i2 h_87 h_71)
                )
            )
          have h_153 : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_negative _value_i2 h_72)
                )
            )
          have h_154 : Litex.Le _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i2 (Litex.number (M := M) 0) h_153)
                )
            )
          have h_155 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i2 (Litex.number (M := M) 0) h_153)
                )
            )
          exact h_72
        )
      )
  )

theorem h_158 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_171 : Litex.In _value_i3 (Litex.Z (M := M))) (h_156 : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i3 (Litex.ZNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_171 h_156
          have h_157 : Litex.In _value_i3 (Litex.ZNeg (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZNeg_intro _value_i3 h_171 h_156)
                )
            )
          have h_222 : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZNeg_negative _value_i3 h_157)
                )
            )
          have h_223 : Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i3 (Litex.number (M := M) 0) h_222)
                )
            )
          have h_224 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i3 (Litex.number (M := M) 0) h_222)
                )
            )
          exact h_157
        )
      )
  )

theorem h_227 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_240 : Litex.In _value_i4 (Litex.R (M := M))) (h_225 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i4 (Litex.RNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_240 h_225
          have h_226 : Litex.In _value_i4 (Litex.RNeg (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_intro _value_i4 h_240 h_225)
                )
            )
          have h_317 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_negative _value_i4 h_226)
                )
            )
          have h_318 : Litex.Le _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i4 (Litex.number (M := M) 0) h_317)
                )
            )
          have h_319 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i4 (Litex.number (M := M) 0) h_317)
                )
            )
          exact h_226
        )
      )
  )

theorem h_322 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_337 : Litex.In _value_i5 (Litex.Q (M := M))) (h_320 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i5 (Litex.QStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_337 h_320
          have h_321 : Litex.In _value_i5 (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_intro _value_i5 h_337 h_320)
                )
            )
          have h_459 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i5 h_321)
                )
            )
          exact h_321
        )
      )
  )

theorem h_462 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_476 : Litex.In _value_i6 (Litex.Z (M := M))) (h_460 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i6 (Litex.ZStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_476 h_460
          have h_461 : Litex.In _value_i6 (Litex.ZStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_intro _value_i6 h_476 h_460)
                )
            )
          have h_531 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i6 h_461)
                )
            )
          exact h_461
        )
      )
  )

theorem h_534 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_548 : Litex.In _value_i7 (Litex.R (M := M))) (h_532 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i7 (Litex.RStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_548 h_532
          have h_533 : Litex.In _value_i7 (Litex.RStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_intro _value_i7 h_548 h_532)
                )
            )
          have h_759 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i7 h_533)
                )
            )
          exact h_533
        )
      )
  )

theorem h_762 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_775 : Litex.In _value_i8 (Litex.C (M := M))) (h_760 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))), Litex.In _value_i8 (Litex.CStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_775 h_760
          have h_761 : Litex.In _value_i8 (Litex.CStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_intro _value_i8 h_775 h_760)
                )
            )
          have h_1035 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i8 h_761)
                )
            )
          exact h_761
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_refined_x5f_numeric_x5f_membership_x2f_statement_x2e_lit
