import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_hierarchy_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (Litex.ZNeg (M := M))), ((Litex.In _value_i1 (Litex.QNeg (M := M))) ∧ (((Litex.In _value_i1 (Litex.RNeg (M := M))) ∧ (((Litex.In _value_i1 (Litex.ZStar (M := M))) ∧ (((Litex.In _value_i1 (Litex.QStar (M := M))) ∧ (((Litex.In _value_i1 (Litex.RStar (M := M))) ∧ (((Litex.In _value_i1 (Litex.CStar (M := M))) ∧ (Litex.In _value_i1 (Litex.C (M := M)))))))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_21
          have h_22 : Litex.Lt _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZNeg_negative _value_i1 h_21)
                )
            )
          have h_23 : Litex.Le _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i1 (Litex.number (M := M) 0) h_22)
                )
            )
          have h_24 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) h_22)
                )
            )
          have h_1 : Litex.In _value_i1 (Litex.QNeg (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_intro _value_i1 (Litex.integerToRational _value_i1 (Litex.inZNeg_base _value_i1 h_21)) (Litex.inZNeg_negative _value_i1 h_21))
                )
            )
          have h_34 : Litex.Lt _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_negative _value_i1 h_1)
                )
            )
          have h_35 : Litex.Le _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i1 (Litex.number (M := M) 0) h_34)
                )
            )
          have h_36 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) h_34)
                )
            )
          have h_2 : Litex.In _value_i1 (Litex.RNeg (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_intro _value_i1 (Litex.rationalToReal _value_i1 (Litex.inQNeg_base _value_i1 h_1)) (Litex.inQNeg_negative _value_i1 h_1))
                )
            )
          have h_55 : Litex.Lt _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_negative _value_i1 h_2)
                )
            )
          have h_56 : Litex.Le _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i1 (Litex.number (M := M) 0) h_55)
                )
            )
          have h_57 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) h_55)
                )
            )
          have h_3 : Litex.In _value_i1 (Litex.ZStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_intro _value_i1 (Litex.inZNeg_base _value_i1 h_21) (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) (Litex.inZNeg_negative _value_i1 h_21)))
                )
            )
          have h_79 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i1 h_3)
                )
            )
          have h_4 : Litex.In _value_i1 (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_intro _value_i1 (Litex.inQNeg_base _value_i1 h_1) (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) (Litex.inQNeg_negative _value_i1 h_1)))
                )
            )
          have h_117 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i1 h_4)
                )
            )
          have h_5 : Litex.In _value_i1 (Litex.RStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_intro _value_i1 (Litex.inRNeg_base _value_i1 h_2) (Litex.ltNotSame _value_i1 (Litex.number (M := M) 0) (Litex.inRNeg_negative _value_i1 h_2)))
                )
            )
          have h_170 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i1 h_5)
                )
            )
          have h_6 : Litex.In _value_i1 (Litex.CStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_intro _value_i1 (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_5)) (Litex.inRStar_nonzero _value_i1 h_5))
                )
            )
          have h_236 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i1 h_6)
                )
            )
          have h_7 : Litex.In _value_i1 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_5))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 (And.intro h_6 h_7))))))
        )
      )
  )

theorem h_341 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_354 : Litex.In _value_i2 (Litex.QPos (M := M))), ((Litex.In _value_i2 (Litex.RPos (M := M))) ∧ (((Litex.In _value_i2 (Litex.QStar (M := M))) ∧ (((Litex.In _value_i2 (Litex.RStar (M := M))) ∧ (Litex.In _value_i2 (Litex.CStar (M := M)))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_354
          have h_355 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_positive _value_i2 h_354)
                )
            )
          have h_356 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_355)
                )
            )
          have h_357 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_355) _litex_zero.symm)
                )
            )
          have h_337 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_intro _value_i2 (Litex.rationalToReal _value_i2 (Litex.inQPos_base _value_i2 h_354)) (Litex.inQPos_positive _value_i2 h_354))
                )
            )
          have h_367 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_337)
                )
            )
          have h_368 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_367)
                )
            )
          have h_369 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_367) _litex_zero.symm)
                )
            )
          have h_338 : Litex.In _value_i2 (Litex.QStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_intro _value_i2 (Litex.inQPos_base _value_i2 h_354) (fun h => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 (Litex.inQPos_positive _value_i2 h_354)) h.symm))
                )
            )
          have h_385 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i2 h_338)
                )
            )
          have h_339 : Litex.In _value_i2 (Litex.RStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_intro _value_i2 (Litex.inRPos_real _value_i2 h_337) (fun h => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 (Litex.inRPos_positive _value_i2 h_337)) h.symm))
                )
            )
          have h_412 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i2 h_339)
                )
            )
          have h_340 : Litex.In _value_i2 (Litex.CStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_intro _value_i2 (Litex.realToComplex _value_i2 (Litex.inRStar_base _value_i2 h_339)) (Litex.inRStar_nonzero _value_i2 h_339))
                )
            )
          have h_451 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i2 h_340)
                )
            )
          exact (And.intro h_337 (And.intro h_338 (And.intro h_339 h_340)))
        )
      )
  )

theorem h_454 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_467 : Litex.In _value_i3 (Litex.NPos (M := M))), ((Litex.In _value_i3 (Litex.QPos (M := M))) ∧ (Litex.In _value_i3 (Litex.ZStar (M := M)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_467
          have h_468 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i3 h_467)
                )
            )
          have h_469 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_468)
                )
            )
          have h_470 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_468) _litex_zero.symm)
                )
            )
          have h_452 : Litex.In _value_i3 (Litex.QPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_intro _value_i3 (Litex.naturalToRational _value_i3 (Litex.inNPos_natural _value_i3 h_467)) (Litex.inNPos_positive _value_i3 h_467))
                )
            )
          have h_480 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_positive _value_i3 h_452)
                )
            )
          have h_481 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_480)
                )
            )
          have h_482 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_480) _litex_zero.symm)
                )
            )
          have h_453 : Litex.In _value_i3 (Litex.ZStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_intro _value_i3 (Litex.naturalToInteger _value_i3 (Litex.inNPos_natural _value_i3 h_467)) (fun h => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 (Litex.inNPos_positive _value_i3 h_467)) h.symm))
                )
            )
          have h_501 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i3 h_453)
                )
            )
          exact (And.intro h_452 h_453)
        )
      )
  )

theorem h_504 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_517 : Litex.In _value_i4 (Litex.QStar (M := M))), ((Litex.In _value_i4 (Litex.RStar (M := M))) ∧ (Litex.In _value_i4 (Litex.CStar (M := M)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_517
          have h_518 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i4 h_517)
                )
            )
          have h_502 : Litex.In _value_i4 (Litex.RStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_intro _value_i4 (Litex.rationalToReal _value_i4 (Litex.inQStar_base _value_i4 h_517)) (Litex.inQStar_nonzero _value_i4 h_517))
                )
            )
          have h_530 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i4 h_502)
                )
            )
          have h_503 : Litex.In _value_i4 (Litex.CStar (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_intro _value_i4 (Litex.realToComplex _value_i4 (Litex.inRStar_base _value_i4 h_502)) (Litex.inRStar_nonzero _value_i4 h_502))
                )
            )
          have h_551 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i4 h_503)
                )
            )
          exact (And.intro h_502 h_503)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_hierarchy_x2f_statement_x2e_lit
