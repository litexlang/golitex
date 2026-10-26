import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_number_x5f_theory_x5f_predicate_x5f_contexts_x2f_statement_x2e_lit

universe u v1 v4 v5 v6 v7 v8 v9 v10 v13 v14 v15 v16
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.N (M := M))) (h_1 : Litex.Prime _value_i1), Litex.Prime _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          have h_17 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_16)
                )
            )
          have h_2 : Litex.Prime _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          exact h_2
        )
      )
  )

theorem h_33 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_47 : Litex.In _value_i4 (Litex.N (M := M))) (h_31 : ¬ Litex.Prime _value_i4), ¬ Litex.Prime _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_47 h_31
          have h_48 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i4 h_47)
                )
            )
          have h_32 : ¬ Litex.Prime _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_31
                )
            )
          exact h_32
        )
      )
  )

theorem h_58 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_71 : Litex.In _value_i5 (Litex.N (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_73 : Litex.In _value_i6 (Litex.N (M := M))) (h_56 : Litex.Coprime _value_i5 _value_i6), Litex.Coprime _value_i5 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_71 _Host_i6 _rep_i6 _value_i6 h_73 h_56
          have h_72 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i5 h_71)
                )
            )
          have h_74 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_73)
                )
            )
          have h_57 : Litex.Coprime _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          exact h_57
        )
      )
  )

theorem h_101 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_115 : Litex.In _value_i7 (Litex.N (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_117 : Litex.In _value_i8 (Litex.N (M := M))) (h_99 : ¬ Litex.Coprime _value_i7 _value_i8), ¬ Litex.Coprime _value_i7 _value_i8 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_115 _Host_i8 _rep_i8 _value_i8 h_117 h_99
          have h_116 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i7 h_115)
                )
            )
          have h_118 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i8 h_117)
                )
            )
          have h_100 : ¬ Litex.Coprime _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_99
                )
            )
          exact h_100
        )
      )
  )

theorem h_137 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_162 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_163 : Litex.In _value_i10 (Litex.ZStar (M := M))) (h_135 : Litex.Dvd _value_i9 _value_i10), Litex.Dvd _value_i9 _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_162 _Host_i10 _rep_i10 _value_i10 h_163 h_135
          have h_164 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i10 h_163)
                )
            )
          have h_136 : Litex.Dvd _value_i9 _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  h_135
                )
            )
          exact h_136
        )
      )
  )

theorem h_193 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_219 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_220 : Litex.In _value_i14 (Litex.ZStar (M := M))) (h_191 : ¬ Litex.Dvd _value_i13 _value_i14), ¬ Litex.Dvd _value_i13 _value_i14 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_219 _Host_i14 _rep_i14 _value_i14 h_220 h_191
          have h_221 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i14 h_220)
                )
            )
          have h_192 : ¬ Litex.Dvd _value_i13 _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  h_191
                )
            )
          exact h_192
        )
      )
  )

theorem h_245 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_258 : Litex.In _value_i15 (Litex.N (M := M))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_260 : Litex.In _value_i16 (Litex.N (M := M))) (h_242 : Litex.Prime _value_i15) (h_243 : Litex.Same _value_i15 _value_i16), Litex.Prime _value_i16 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_258 _Host_i16 _rep_i16 _value_i16 h_260 h_242 h_243
          have h_259 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i15 h_258)
                )
            )
          have h_261 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i16 h_260)
                )
            )
          have h_244 : Litex.Prime _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (Litex.PrimeValue M _known_argument_0)) (Litex.denote _value_i16)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (Litex.PrimeValue M _known_argument_0)) (Litex.denote _value_i15)) := h_242
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (Litex.PrimeValue M _known_argument_0)) (Litex.denote _value_i15)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (Litex.PrimeValue M _known_argument_0)) _known_value)) h_243)) _known_citation
                  )
                )
            )
          exact h_244
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_number_x5f_theory_x5f_predicate_x5f_contexts_x2f_statement_x2e_lit
