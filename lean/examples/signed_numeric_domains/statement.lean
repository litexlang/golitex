import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_domains_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.QPos (M := M))), (by
  have h_17 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inQPos_positive _value_i1 h_16)
        )
    )
  have h_19 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_17) _litex_zero.symm)
        )
    )
  let _object_w3 := (Litex.div _value_i1 _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)) (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)) h_19)
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1) ∧ ((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16
          have h_17 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_positive _value_i1 h_16)
                )
            )
          have h_18 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_17)
                )
            )
          have h_19 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_17) _litex_zero.symm)
                )
            )
          have h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          let _object_w3 := (Litex.div _value_i1 _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)) (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)) h_19)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16))) / (Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_16))) h_19
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_209 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_222 : Litex.In _value_i2 (Litex.QNeg (M := M))), (by
  have h_223 : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inQNeg_negative _value_i2 h_222)
        )
    )
  have h_225 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltNotSame _value_i2 (Litex.number (M := M) 0) h_223)
        )
    )
  let _object_w7 := (Litex.div _value_i2 _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)) (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)) h_225)
  exact ((Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w7
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_222
          have h_223 : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_negative _value_i2 h_222)
                )
            )
          have h_224 : Litex.Le _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i2 (Litex.number (M := M) 0) h_223)
                )
            )
          have h_225 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i2 (Litex.number (M := M) 0) h_223)
                )
            )
          have h_207 : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_223
                )
            )
          let _object_w7 := (Litex.div _value_i2 _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)) (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)) h_225)
          have h_208 : (by
            let _equal_wd_1_0 := _object_w7
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222))) / (Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_222))) h_225
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_207 h_208)
        )
      )
  )

theorem h_449 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_462 : Litex.In _value_i3 (Litex.ZNeg (M := M))), (by
  have h_463 : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inZNeg_negative _value_i3 h_462)
        )
    )
  have h_465 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltNotSame _value_i3 (Litex.number (M := M) 0) h_463)
        )
    )
  let _object_w11 := (Litex.div _value_i3 _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)) (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)) h_465)
  exact ((Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w11
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_462
          have h_463 : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZNeg_negative _value_i3 h_462)
                )
            )
          have h_464 : Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i3 (Litex.number (M := M) 0) h_463)
                )
            )
          have h_465 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i3 (Litex.number (M := M) 0) h_463)
                )
            )
          have h_447 : Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_464
                )
            )
          let _object_w11 := (Litex.div _value_i3 _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)) (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)) h_465)
          have h_448 : (by
            let _equal_wd_1_0 := _object_w11
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462))) / (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i3 _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_462))) h_465
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_447 h_448)
        )
      )
  )

theorem h_740 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_753 : Litex.In _value_i4 (Litex.RNeg (M := M))), (by
  have h_754 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRNeg_negative _value_i4 h_753)
        )
    )
  have h_756 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltNotSame _value_i4 (Litex.number (M := M) 0) h_754)
        )
    )
  let _object_w15 := (Litex.div _value_i4 _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)) (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)) h_756)
  exact ((Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w15
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_753
          have h_754 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_negative _value_i4 h_753)
                )
            )
          have h_755 : Litex.Le _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i4 (Litex.number (M := M) 0) h_754)
                )
            )
          have h_756 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i4 (Litex.number (M := M) 0) h_754)
                )
            )
          have h_738 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_754
                )
            )
          let _object_w15 := (Litex.div _value_i4 _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)) (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)) h_756)
          have h_739 : (by
            let _equal_wd_1_0 := _object_w15
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753))) / (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i4 _value_i4 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i4 (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_753))) h_756
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_738 h_739)
        )
      )
  )

theorem h_953 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_966 : Litex.In _value_i5 (Litex.QStar (M := M))), (by
  have h_967 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inQStar_nonzero _value_i5 h_966)
        )
    )
  let _object_w19 := (Litex.div _value_i5 _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)) (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)) h_967)
  exact ((¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w19
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_966
          have h_967 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i5 h_966)
                )
            )
          have h_951 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_967
                )
            )
          let _object_w19 := (Litex.div _value_i5 _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)) (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)) h_967)
          have h_952 : (by
            let _equal_wd_1_0 := _object_w19
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966))) / (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i5 _value_i5 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966))) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i5 (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966))) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_966))) h_967
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_951 h_952)
        )
      )
  )

theorem h_1148 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1161 : Litex.In _value_i6 (Litex.ZStar (M := M))), (by
  have h_1162 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inZStar_nonzero _value_i6 h_1161)
        )
    )
  let _object_w23 := (Litex.div _value_i6 _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)) (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)) h_1162)
  exact ((¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w23
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_1161
          have h_1162 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i6 h_1161)
                )
            )
          have h_1146 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1162
                )
            )
          let _object_w23 := (Litex.div _value_i6 _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)) (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)) h_1162)
          have h_1147 : (by
            let _equal_wd_1_0 := _object_w23
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w23;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161))) / (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i6 _value_i6 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i6 (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1161))) h_1162
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_1146 h_1147)
        )
      )
  )

theorem h_1367 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1380 : Litex.In _value_i7 (Litex.RStar (M := M))), (by
  have h_1381 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRStar_nonzero _value_i7 h_1380)
        )
    )
  let _object_w27 := (Litex.div _value_i7 _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)) (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)) h_1381)
  exact ((¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w27
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_1380
          have h_1381 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i7 h_1380)
                )
            )
          have h_1365 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1381
                )
            )
          let _object_w27 := (Litex.div _value_i7 _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)) (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)) h_1381)
          have h_1366 : (by
            let _equal_wd_1_0 := _object_w27
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w27;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380))) / (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i7 _value_i7 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380))) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i7 (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380))) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1380))) h_1381
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_1365 h_1366)
        )
      )
  )

theorem h_1538 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_1551 : Litex.In _value_i8 (Litex.CStar (M := M))), (by
  have h_1552 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inCStar_nonzero _value_i8 h_1551)
        )
    )
  let _object_w31 := (Litex.div _value_i8 _value_i8 (Litex.inCStar_base _value_i8 h_1551) (Litex.inCStar_base _value_i8 h_1551) h_1552)
  exact ((¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))) ∧ ((by
    let _equal_wd_1_0 := _object_w31
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_1551
          have h_1552 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i8 h_1551)
                )
            )
          have h_1536 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1552
                )
            )
          let _object_w31 := (Litex.div _value_i8 _value_i8 (Litex.inCStar_base _value_i8 h_1551) (Litex.inCStar_base _value_i8 h_1551) h_1552)
          have h_1537 : (by
            let _equal_wd_1_0 := _object_w31
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w31;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_1551)) / (Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_1551))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i8 _value_i8 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_1551)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_1551))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_1551)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i8 (Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_1551)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_1551)) h_1552
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          exact (And.intro h_1536 h_1537)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_domains_x2f_statement_x2e_lit
