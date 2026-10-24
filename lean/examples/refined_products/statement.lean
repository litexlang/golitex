import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_refined_x5f_products_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_28 : Litex.In _value_i1 (Litex.RPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.RPos (M := M))), (by
  have h_33 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_32)
        )
    )
  have h_35 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_33) _litex_zero.symm)
        )
    )
  let _object_w3 := (Litex.mul _value_i1 _value_i2 (Litex.positiveRealToComplex _value_i1 h_28) (Litex.positiveRealToComplex _value_i2 h_32))
  let _object_w4 := (Litex.div _value_i1 _value_i2 (Litex.positiveRealToComplex _value_i1 h_28) (Litex.positiveRealToComplex _value_i2 h_32) h_35)
  exact (((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_28 _Host_i2 _rep_i2 _value_i2 h_32
          have h_29 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_28)
                )
            )
          have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_29)
                )
            )
          have h_31 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_29) _litex_zero.symm)
                )
            )
          have h_33 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_32)
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_33)
                )
            )
          have h_35 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_33) _litex_zero.symm)
                )
            )
          let _object_w3 := (Litex.mul _value_i1 _value_i2 (Litex.positiveRealToComplex _value_i1 h_28) (Litex.positiveRealToComplex _value_i2 h_32))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.mulInRPos _atomic_wd_1_0 h_28 h_32))
                )
            )
          have h_111 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_w3 h_1)
                )
            )
          have h_112 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w3 h_111)
                )
            )
          have h_113 : ¬ Litex.Same _object_w3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w3 h_111) _litex_zero.symm)
                )
            )
          let _object_w4 := (Litex.div _value_i1 _value_i2 (Litex.positiveRealToComplex _value_i1 h_28) (Litex.positiveRealToComplex _value_i2 h_32) h_35)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.divInRPos _atomic_wd_1_0 h_28 h_32))
                )
            )
          have h_214 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_w4 h_2)
                )
            )
          have h_215 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w4 h_214)
                )
            )
          have h_216 : ¬ Litex.Same _object_w4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w4 h_214) _litex_zero.symm)
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_219 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_244 : Litex.In _value_i3 (Litex.QStar (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_246 : Litex.In _value_i4 (Litex.QStar (M := M))), (by
  have h_247 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inQStar_nonzero _value_i4 h_246)
        )
    )
  let _object_w7 := (Litex.mul _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_244)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_246)))
  let _object_w8 := (Litex.div _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_244)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_246)) h_247)
  exact (((by
    let _atomic_wd_1_0 := _object_w7
    exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w8
    exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_244 _Host_i4 _rep_i4 _value_i4 h_246
          have h_245 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i3 h_244)
                )
            )
          have h_247 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i4 h_246)
                )
            )
          let _object_w7 := (Litex.mul _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_244)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_246)))
          have h_217 : (by
            let _atomic_wd_1_0 := _object_w7
            exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (Litex.mulInQStar _atomic_wd_1_0 h_244 h_246))
                )
            )
          have h_330 : ¬ Litex.Same _object_w7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _object_w7 h_217)
                )
            )
          let _object_w8 := (Litex.div _value_i3 _value_i4 (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_244)) (Litex.rationalToComplex _value_i4 (Litex.inQStar_base _value_i4 h_246)) h_247)
          have h_218 : (by
            let _atomic_wd_1_0 := _object_w8
            exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    exact (Litex.divInQStar _atomic_wd_1_0 h_244 h_246))
                )
            )
          have h_439 : ¬ Litex.Same _object_w8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _object_w8 h_218)
                )
            )
          exact (And.intro h_217 h_218)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_refined_x5f_products_x2f_statement_x2e_lit
