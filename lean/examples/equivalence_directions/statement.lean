import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equivalence_x5f_directions_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
variable {M : Litex.Semantics.{u}}

theorem h_4 : ((∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i1) ∧ (∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_33 : Litex.In _value_i1 (Litex.R (M := M))) (h_2 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i1), Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        ⟨(by
          intro _Host_i1 _rep_i1 _value_i1 h_19 h_1
          have h_2 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (h_1).symm
                )
            )
          exact h_2
        ), (by
          intro _Host_i1 _rep_i1 _value_i1 h_33 h_2
          have h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).symm
                )
            )
          exact h_1
        )⟩
      )
  )

theorem h_35 : ((fun {p q : Prop} (_ : p ∧ q) => p) (h_4 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_4 (M := M))).1
      )
  )

theorem h_36 : ((fun {p q : Prop} (_ : p ∧ q) => q) (h_4 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_4 (M := M))).2
      )
  )

theorem h_39 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_42 : Litex.In _value_i2 (Litex.R (M := M))) (h_37 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_42 h_37
          exact ((h_35 (M := M)) _value_i2 h_42 h_37)
        )
      )
  )

theorem h_45 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_49 : Litex.In _value_i3 (Litex.R (M := M))) (h_43 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i3), Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_49 h_43
          exact ((h_36 (M := M)) _value_i3 h_49 h_43)
        )
      )
  )

theorem h_54 : ((∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_69 : Litex.In _value_i4 (Litex.R (M := M))) (h_50 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_51 : (by
  let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_69) (M.real_subset_complex _ h_69) h_50)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))), (by
  let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_69) (M.real_subset_complex _ h_69) h_50)
  exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1)) ∧ (∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_108 : Litex.In _value_i4 (Litex.R (M := M))) (h_50 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_52 : (by
  let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_108) (M.real_subset_complex _ h_108) h_50)
  exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1)), (by
  let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_108) (M.real_subset_complex _ h_108) h_50)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        ⟨(by
          intro _Host_i4 _rep_i4 _value_i4 h_69 h_50 h_51
          have h_52 : (by
            let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_69) (M.real_subset_complex _ h_69) h_50)
            exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (h_51).symm
                )
            )
          exact h_52
        ), (by
          intro _Host_i4 _rep_i4 _value_i4 h_108 h_50 h_52
          have h_51 : (by
            let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_108) (M.real_subset_complex _ h_108) h_50)
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).symm
                )
            )
          exact h_51
        )⟩
      )
  )

theorem h_135 : ((fun {p q : Prop} (_ : p ∧ q) => p) (h_54 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_54 (M := M))).1
      )
  )

theorem h_136 : ((fun {p q : Prop} (_ : p ∧ q) => q) (h_54 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_54 (M := M))).2
      )
  )

theorem h_139 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_144 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_145 : Litex.In _value_i6 (Litex.R (M := M))) (h_137 : Litex.Same _value_i5 _value_i6), Litex.Same _value_i6 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_144 _Host_i6 _rep_i6 _value_i6 h_145 h_137
          have h_146 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_144
                )
            )
          have h_147 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_145
                )
            )
          have h_143 : ((∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_162 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_163 : Litex.In _value_i8 (Litex.R (M := M))) (h_140 : Litex.Same _value_i7 _value_i8), Litex.Same _value_i8 _value_i7) ∧ (∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_177 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_178 : Litex.In _value_i8 (Litex.R (M := M))) (h_141 : Litex.Same _value_i8 _value_i7), Litex.Same _value_i7 _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  ⟨(by
                    intro _Host_i7 _rep_i7 _value_i7 h_162 _Host_i8 _rep_i8 _value_i8 h_163 h_140
                    have h_141 : Litex.Same _value_i8 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (h_140).symm
                          )
                      )
                    exact h_141
                  ), (by
                    intro _Host_i7 _rep_i7 _value_i7 h_177 _Host_i8 _rep_i8 _value_i8 h_178 h_141
                    have h_140 : Litex.Same _value_i7 _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (h_141).symm
                          )
                      )
                    exact h_140
                  )⟩
                )
            )

          have h_180 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_143) :=
            (by
              litex_checked_step =>
                exact (
                  (h_143).1
                )
            )

          have h_181 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_143) :=
            (by
              litex_checked_step =>
                exact (
                  (h_143).2
                )
            )
          exact (h_137).symm
        )
      )
  )

theorem h_191 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_192 : Litex.In _value_i10 (Litex.R (M := M))) (h_188 : ((∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_193 : Litex.In _value_i11 (Litex.R (M := M))) (h_185 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i11) ∧ (∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_193 : Litex.In _value_i11 (Litex.R (M := M))) (h_186 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i11), Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))))) (h_189 : Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_192 h_188 h_189
          have h_194 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_188) :=
            (by
              litex_checked_step =>
                exact (
                  (h_188).1
                )
            )
          have h_195 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_188) :=
            (by
              litex_checked_step =>
                exact (
                  (h_188).2
                )
            )
          have h_196 : Litex.In _value_i10 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_192
                )
            )
          have h_198 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_188) :=
            (by
              litex_checked_step =>
                exact (
                  (h_188).1
                )
            )
          have h_199 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_188) :=
            (by
              litex_checked_step =>
                exact (
                  (h_188).2
                )
            )
          exact (h_189).symm
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equivalence_x5f_directions_x2f_statement_x2e_lit
