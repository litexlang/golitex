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

theorem h_39 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_43 : Litex.In _value_i2 (Litex.R (M := M))) (h_37 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_43 h_37
          exact ((h_35 (M := M)) _value_i2 h_43 h_37)
        )
      )
  )

theorem h_46 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_50 : Litex.In _value_i3 (Litex.R (M := M))) (h_44 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i3), Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_50 h_44
          exact ((h_36 (M := M)) _value_i3 h_50 h_44)
        )
      )
  )

theorem h_55 : ((∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_70 : Litex.In _value_i4 (Litex.R (M := M))) (h_51 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_52 : (by
  let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_70) (M.real_subset_complex _ h_70) h_51)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))), (by
  let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_70) (M.real_subset_complex _ h_70) h_51)
  exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1)) ∧ (∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_109 : Litex.In _value_i4 (Litex.R (M := M))) (h_51 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_53 : (by
  let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_109) (M.real_subset_complex _ h_109) h_51)
  exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1)), (by
  let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_109) (M.real_subset_complex _ h_109) h_51)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        ⟨(by
          intro _Host_i4 _rep_i4 _value_i4 h_70 h_51 h_52
          have h_53 : (by
            let _equal_wd_1_1 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_70) (M.real_subset_complex _ h_70) h_51)
            exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).symm
                )
            )
          exact h_53
        ), (by
          intro _Host_i4 _rep_i4 _value_i4 h_109 h_51 h_53
          have h_52 : (by
            let _equal_wd_1_0 := (Litex.div _value_i4 _value_i4 (M.real_subset_complex _ h_109) (M.real_subset_complex _ h_109) h_51)
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_53).symm
                )
            )
          exact h_52
        )⟩
      )
  )

theorem h_136 : ((fun {p q : Prop} (_ : p ∧ q) => p) (h_55 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_55 (M := M))).1
      )
  )

theorem h_137 : ((fun {p q : Prop} (_ : p ∧ q) => q) (h_55 (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_55 (M := M))).2
      )
  )

theorem h_140 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_145 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_146 : Litex.In _value_i6 (Litex.R (M := M))) (h_138 : Litex.Same _value_i5 _value_i6), Litex.Same _value_i6 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_145 _Host_i6 _rep_i6 _value_i6 h_146 h_138
          have h_147 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_145
                )
            )
          have h_148 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_146
                )
            )
          have h_144 : ((∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_163 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_164 : Litex.In _value_i8 (Litex.R (M := M))) (h_141 : Litex.Same _value_i7 _value_i8), Litex.Same _value_i8 _value_i7) ∧ (∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_178 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_179 : Litex.In _value_i8 (Litex.R (M := M))) (h_142 : Litex.Same _value_i8 _value_i7), Litex.Same _value_i7 _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  ⟨(by
                    intro _Host_i7 _rep_i7 _value_i7 h_163 _Host_i8 _rep_i8 _value_i8 h_164 h_141
                    have h_142 : Litex.Same _value_i8 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (h_141).symm
                          )
                      )
                    exact h_142
                  ), (by
                    intro _Host_i7 _rep_i7 _value_i7 h_178 _Host_i8 _rep_i8 _value_i8 h_179 h_142
                    have h_141 : Litex.Same _value_i7 _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (h_142).symm
                          )
                      )
                    exact h_141
                  )⟩
                )
            )

          have h_181 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_144) :=
            (by
              litex_checked_step =>
                exact (
                  (h_144).1
                )
            )

          have h_182 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_144) :=
            (by
              litex_checked_step =>
                exact (
                  (h_144).2
                )
            )
          exact (h_138).symm
        )
      )
  )

theorem h_192 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_193 : Litex.In _value_i10 (Litex.R (M := M))) (h_189 : ((∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_194 : Litex.In _value_i11 (Litex.R (M := M))) (h_186 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i11) ∧ (∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_194 : Litex.In _value_i11 (Litex.R (M := M))) (h_187 : Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i11), Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))))) (h_190 : Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_193 h_189 h_190
          have h_195 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_189) :=
            (by
              litex_checked_step =>
                exact (
                  (h_189).1
                )
            )
          have h_196 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_189) :=
            (by
              litex_checked_step =>
                exact (
                  (h_189).2
                )
            )
          have h_197 : Litex.In _value_i10 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_193
                )
            )
          have h_199 : ((fun {p q : Prop} (_ : p ∧ q) => p) h_189) :=
            (by
              litex_checked_step =>
                exact (
                  (h_189).1
                )
            )
          have h_200 : ((fun {p q : Prop} (_ : p ∧ q) => q) h_189) :=
            (by
              litex_checked_step =>
                exact (
                  (h_189).2
                )
            )
          exact (h_190).symm
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equivalence_x5f_directions_x2f_statement_x2e_lit
