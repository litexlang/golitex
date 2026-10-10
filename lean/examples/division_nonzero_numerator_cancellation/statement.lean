import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_nonzero_x5f_numerator_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_20 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) (h_2 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_3 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) (h_4 : Litex.Same (Litex.div _value_i3 _value_i1 (Litex.realToComplex _value_i3 h_21) (Litex.realToComplex _value_i1 h_19) h_2) (Litex.div _value_i3 _value_i2 (Litex.realToComplex _value_i3 h_21) (Litex.realToComplex _value_i2 h_20) h_3)), Litex.Same _value_i1 _value_i2 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_20 _Host_i3 _rep_i3 _value_i3 h_21 h_1 h_2 h_3 h_4
    have h_182 : Litex.Same _value_i1 _value_i2 :=
      (Litex.divCancelNonzeroNumerator _value_i1 _value_i2 _value_i3 (Litex.realToComplex _value_i1 h_19) (Litex.realToComplex _value_i2 h_20) (Litex.realToComplex _value_i3 h_21) h_1 h_2 h_3 h_4)
    have h_5 : Litex.Same _value_i1 _value_i2 :=
      (((Litex.sameRefl _value_i1)).trans h_182)
    exact h_5
  )

theorem h_189 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_202 : Litex.In _value_i4 (Litex.C (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_203 : Litex.In _value_i5 (Litex.C (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_204 : Litex.In _value_i6 (Litex.C (M := M))) (h_184 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) (h_185 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_186 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) (h_187 : Litex.Same (Litex.div _value_i6 _value_i4 h_204 h_202 h_185) (Litex.div _value_i6 _value_i5 h_204 h_203 h_186)), Litex.Same _value_i4 _value_i5 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_202 _Host_i5 _rep_i5 _value_i5 h_203 _Host_i6 _rep_i6 _value_i6 h_204 h_184 h_185 h_186 h_187
    have h_296 : Litex.Same _value_i4 _value_i5 :=
      (Litex.divCancelNonzeroNumerator _value_i4 _value_i5 _value_i6 h_202 h_203 h_204 h_184 h_185 h_186 h_187)
    have h_188 : Litex.Same _value_i4 _value_i5 :=
      (((Litex.sameRefl _value_i4)).trans h_296)
    exact h_188
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_nonzero_x5f_numerator_x5f_cancellation_x2f_statement_x2e_lit
