import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_subtractive_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Same (Litex.sub _value_i1 _value_i3 (Litex.realToComplex _value_i1 h_16) (Litex.realToComplex _value_i3 h_18)) (Litex.sub _value_i2 _value_i3 (Litex.realToComplex _value_i2 h_17) (Litex.realToComplex _value_i3 h_18))), Litex.Same _value_i1 _value_i2 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18 h_1
    have h_139 : Litex.Same _value_i1 _value_i2 :=
      (Litex.subCancelRightRight _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 h_16) (Litex.realToComplex _value_i2 h_17) (Litex.realToComplex _value_i3 h_18) h_1)
    have h_2 : Litex.Same _value_i1 _value_i2 :=
      (((Litex.sameRefl _value_i1)).trans h_139)
    exact h_2
  )

theorem h_143 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_156 : Litex.In _value_i4 (Litex.C (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_157 : Litex.In _value_i5 (Litex.C (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_158 : Litex.In _value_i6 (Litex.C (M := M))) (h_141 : Litex.Same (Litex.sub _value_i6 _value_i4 h_158 h_156) (Litex.sub _value_i6 _value_i5 h_158 h_157)), Litex.Same _value_i4 _value_i5 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_156 _Host_i5 _rep_i5 _value_i5 h_157 _Host_i6 _rep_i6 _value_i6 h_158 h_141
    have h_210 : Litex.Same _value_i4 _value_i5 :=
      (Litex.subCancelLeftLeft _value_i4 _value_i5 _value_i6 h_156 h_157 h_158 h_141)
    have h_142 : Litex.Same _value_i4 _value_i5 :=
      (((Litex.sameRefl _value_i4)).trans h_210)
    exact h_142
  )

theorem h_214 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_227 : Litex.In _value_i7 (Litex.Q (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_228 : Litex.In _value_i8 (Litex.Q (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_229 : Litex.In _value_i9 (Litex.Q (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_230 : Litex.In _value_i10 (Litex.Q (M := M))) (h_212 : Litex.Same (Litex.sub (Litex.sub _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i9 h_229)) _value_i10 (Litex.subInC _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i9 h_229)) (Litex.rationalToComplex _value_i10 h_230)) (Litex.sub (Litex.sub _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229)) _value_i10 (Litex.subInC _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229)) (Litex.rationalToComplex _value_i10 h_230))), Litex.Same _value_i7 _value_i8 :=
  (by
    intro _Host_i7 _rep_i7 _value_i7 h_227 _Host_i8 _rep_i8 _value_i8 h_228 _Host_i9 _rep_i9 _value_i9 h_229 _Host_i10 _rep_i10 _value_i10 h_230 h_212
    have h_744 : Litex.Same (Litex.sub _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i9 h_229)) (Litex.sub _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229)) :=
      (Litex.subCancelRightRight (Litex.sub _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i9 h_229)) (Litex.sub _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229)) _value_i10 (Litex.subInC _value_i7 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i9 h_229)) (Litex.subInC _value_i8 _value_i9 (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229)) (Litex.rationalToComplex _value_i10 h_230) h_212)
    have h_906 : Litex.Same _value_i7 _value_i8 :=
      (Litex.subCancelRightRight _value_i7 _value_i8 _value_i9 (Litex.rationalToComplex _value_i7 h_227) (Litex.rationalToComplex _value_i8 h_228) (Litex.rationalToComplex _value_i9 h_229) h_744)
    have h_213 : Litex.Same _value_i7 _value_i8 :=
      (((Litex.sameRefl _value_i7)).trans h_906)
    exact h_213
  )
end LitexCompiled.file_lean_x2f_examples_x2f_subtractive_x5f_cancellation_x2f_statement_x2e_lit
