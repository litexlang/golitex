import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_common_x5f_denominator_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same (Litex.div _value_i1 _value_i3 (Litex.realToComplex _value_i1 h_17) (Litex.realToComplex _value_i3 h_19) h_1) (Litex.div _value_i2 _value_i3 (Litex.realToComplex _value_i2 h_18) (Litex.realToComplex _value_i3 h_19) h_1)), Litex.Same _value_i1 _value_i2 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
    have h_155 : Litex.Same _value_i1 _value_i2 :=
      (Litex.divCancelCommonDenominator _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 h_17) (Litex.realToComplex _value_i2 h_18) (Litex.realToComplex _value_i3 h_19) h_1 h_2)
    have h_3 : Litex.Same _value_i1 _value_i2 :=
      (((Litex.sameRefl _value_i1)).trans h_155)
    exact h_3
  )

theorem h_160 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_173 : Litex.In _value_i4 (Litex.C (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_174 : Litex.In _value_i5 (Litex.C (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_175 : Litex.In _value_i6 (Litex.C (M := M))) (h_157 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) (h_158 : Litex.Same (Litex.div _value_i4 _value_i6 h_173 h_175 h_157) (Litex.div _value_i5 _value_i6 h_174 h_175 h_157)), Litex.Same _value_i4 _value_i5 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_173 _Host_i5 _rep_i5 _value_i5 h_174 _Host_i6 _rep_i6 _value_i6 h_175 h_157 h_158
    have h_242 : Litex.Same _value_i4 _value_i5 :=
      (Litex.divCancelCommonDenominator _value_i4 _value_i5 _value_i6 h_173 h_174 h_175 h_157 h_158)
    have h_159 : Litex.Same _value_i4 _value_i5 :=
      (((Litex.sameRefl _value_i4)).trans h_242)
    exact h_159
  )

theorem h_248 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_261 : Litex.In _value_i7 (Litex.Q (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_262 : Litex.In _value_i8 (Litex.Q (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_263 : Litex.In _value_i9 (Litex.Q (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_264 : Litex.In _value_i10 (Litex.Q (M := M))) (h_244 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) (h_245 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))) (h_246 : Litex.Same (Litex.div (Litex.div _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) h_244) _value_i10 (Litex.divInC _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) ((Litex.div _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) h_244)).wd.2.2) (Litex.rationalToComplex _value_i10 h_264) h_245) (Litex.div (Litex.div _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244) _value_i10 (Litex.divInC _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) ((Litex.div _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244)).wd.2.2) (Litex.rationalToComplex _value_i10 h_264) h_245)), Litex.Same _value_i7 _value_i8 :=
  (by
    intro _Host_i7 _rep_i7 _value_i7 h_261 _Host_i8 _rep_i8 _value_i8 h_262 _Host_i9 _rep_i9 _value_i9 h_263 _Host_i10 _rep_i10 _value_i10 h_264 h_244 h_245 h_246
    have h_830 : Litex.Same (Litex.div _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) h_244) (Litex.div _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244) :=
      (Litex.divCancelCommonDenominator (Litex.div _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) h_244) (Litex.div _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244) _value_i10 (Litex.divInC _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) ((Litex.div _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i9 h_263) h_244)).wd.2.2) (Litex.divInC _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) ((Litex.div _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244)).wd.2.2) (Litex.rationalToComplex _value_i10 h_264) h_245 h_246)
    have h_1007 : Litex.Same _value_i7 _value_i8 :=
      (Litex.divCancelCommonDenominator _value_i7 _value_i8 _value_i9 (Litex.rationalToComplex _value_i7 h_261) (Litex.rationalToComplex _value_i8 h_262) (Litex.rationalToComplex _value_i9 h_263) h_244 h_830)
    have h_247 : Litex.Same _value_i7 _value_i8 :=
      (((Litex.sameRefl _value_i7)).trans h_1007)
    exact h_247
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_common_x5f_denominator_x5f_cancellation_x2f_statement_x2e_lit
