import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_multiplicative_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same (Litex.mul _value_i1 _value_i3 (Litex.realToComplex _value_i1 h_17) (Litex.realToComplex _value_i3 h_19)) (Litex.mul _value_i2 _value_i3 (Litex.realToComplex _value_i2 h_18) (Litex.realToComplex _value_i3 h_19))), Litex.Same _value_i1 _value_i2 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
    have h_145 : Litex.Same _value_i1 _value_i2 :=
      (Litex.mulCancelRightRight _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 h_17) (Litex.realToComplex _value_i2 h_18) (Litex.realToComplex _value_i3 h_19) h_1 h_2)
    have h_3 : Litex.Same _value_i1 _value_i2 :=
      (((Litex.sameRefl _value_i1)).trans h_145)
    exact h_3
  )

theorem h_150 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_163 : Litex.In _value_i4 (Litex.C (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_164 : Litex.In _value_i5 (Litex.C (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_165 : Litex.In _value_i6 (Litex.C (M := M))) (h_147 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) (h_148 : Litex.Same (Litex.mul _value_i4 _value_i6 h_163 h_165) (Litex.mul _value_i6 _value_i5 h_165 h_164)), Litex.Same _value_i4 _value_i5 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_163 _Host_i5 _rep_i5 _value_i5 h_164 _Host_i6 _rep_i6 _value_i6 h_165 h_147 h_148
    have h_222 : Litex.Same _value_i4 _value_i5 :=
      (Litex.mulCancelRightLeft _value_i4 _value_i5 _value_i6 h_163 h_164 h_165 h_147 h_148)
    have h_149 : Litex.Same _value_i4 _value_i5 :=
      (((Litex.sameRefl _value_i4)).trans h_222)
    exact h_149
  )

theorem h_227 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_242 : Litex.In _value_i7 (Litex.C (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_243 : Litex.In _value_i8 (Litex.C (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_244 : Litex.In _value_i9 (Litex.C (M := M))) (h_224 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) (h_225 : Litex.Same (Litex.mul _value_i9 _value_i7 h_244 h_242) (Litex.mul _value_i8 _value_i9 h_243 h_244)), Litex.Same _value_i7 _value_i8 :=
  (by
    intro _Host_i7 _rep_i7 _value_i7 h_242 _Host_i8 _rep_i8 _value_i8 h_243 _Host_i9 _rep_i9 _value_i9 h_244 h_224 h_225
    have h_301 : Litex.Same _value_i7 _value_i8 :=
      (Litex.mulCancelLeftRight _value_i7 _value_i8 _value_i9 h_242 h_243 h_244 h_224 h_225)
    have h_226 : Litex.Same _value_i7 _value_i8 :=
      (((Litex.sameRefl _value_i7)).trans h_301)
    exact h_226
  )

theorem h_306 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_321 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_322 : Litex.In _value_i11 (Litex.R (M := M))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_323 : Litex.In _value_i12 (Litex.R (M := M))) (h_303 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))) (h_304 : Litex.Same (Litex.mul _value_i12 _value_i10 (Litex.realToComplex _value_i12 h_323) (Litex.realToComplex _value_i10 h_321)) (Litex.mul _value_i12 _value_i11 (Litex.realToComplex _value_i12 h_323) (Litex.realToComplex _value_i11 h_322))), Litex.Same _value_i10 _value_i11 :=
  (by
    intro _Host_i10 _rep_i10 _value_i10 h_321 _Host_i11 _rep_i11 _value_i11 h_322 _Host_i12 _rep_i12 _value_i12 h_323 h_303 h_304
    have h_449 : Litex.Same _value_i10 _value_i11 :=
      (Litex.mulCancelLeftLeft _value_i10 _value_i11 _value_i12 (Litex.realToComplex _value_i10 h_321) (Litex.realToComplex _value_i11 h_322) (Litex.realToComplex _value_i12 h_323) h_303 h_304)
    have h_305 : Litex.Same _value_i10 _value_i11 :=
      (((Litex.sameRefl _value_i10)).trans h_449)
    exact h_305
  )

theorem h_456 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_469 : Litex.In _value_i13 (Litex.Q (M := M))) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_470 : Litex.In _value_i14 (Litex.Q (M := M))) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_471 : Litex.In _value_i15 (Litex.Q (M := M))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_472 : Litex.In _value_i16 (Litex.Q (M := M))) (h_451 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))) (h_452 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))) (h_453 : Litex.Same (Litex.mul (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) _value_i16 (Litex.mulInC _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.rationalToComplex _value_i16 h_472)) (Litex.mul (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) _value_i16 (Litex.mulInC _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) (Litex.rationalToComplex _value_i16 h_472))), (Litex.Same (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) ∧ Litex.Same _value_i13 _value_i14) :=
  (by
    intro _Host_i13 _rep_i13 _value_i13 h_469 _Host_i14 _rep_i14 _value_i14 h_470 _Host_i15 _rep_i15 _value_i15 h_471 _Host_i16 _rep_i16 _value_i16 h_472 h_451 h_452 h_453
    have h_994 : Litex.Same (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) :=
      (Litex.mulCancelRightRight (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) _value_i16 (Litex.mulInC _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.mulInC _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) (Litex.rationalToComplex _value_i16 h_472) h_452 h_453)
    have h_454 : Litex.Same (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)) (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471)) :=
      (((Litex.sameRefl (Litex.mul _value_i13 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i15 h_471)))).trans h_994)
    have h_1070 : Litex.Same _value_i13 _value_i14 :=
      (Litex.mulCancelRightRight _value_i13 _value_i14 _value_i15 (Litex.rationalToComplex _value_i13 h_469) (Litex.rationalToComplex _value_i14 h_470) (Litex.rationalToComplex _value_i15 h_471) h_451 h_454)
    have h_455 : Litex.Same _value_i13 _value_i14 :=
      (((Litex.sameRefl _value_i13)).trans h_1070)
    exact (And.intro h_454 h_455)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_multiplicative_x5f_cancellation_x2f_statement_x2e_lit
