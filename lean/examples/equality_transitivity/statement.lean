import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_transitivity_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7
variable {M : Litex.Semantics.{u}}

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_20 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Same _value_i1 _value_i2) (h_2 : Litex.Same _value_i2 _value_i3), (by
  have h_3 : Litex.Same _value_i1 _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          ((h_1).trans h_2)
        )
    )
  let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_19) (Litex.numberInC (M := M) (1 : ℂ)))
  let _object_w3 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (Litex.inOfSame _value_i1 _value_i3 (Litex.R (M := M)) (Litex.R (M := M)) h_3 (show @Eq M.Value _ _ from Eq.refl _) h_19)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact ((Litex.Same _value_i1 _value_i3) ∧ (((Litex.Same _value_i3 _value_i1) ∧ ((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_20 _Host_i3 _rep_i3 _value_i3 h_21 h_1 h_2
          have h_3 : Litex.Same _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  ((h_1).trans h_2)
                )
            )
          have h_4 : Litex.Same _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (h_3).symm
                )
            )
          let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_19) (Litex.numberInC (M := M) (1 : ℂ)))
          let _object_w3 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (Litex.inOfSame _value_i1 _value_i3 (Litex.R (M := M)) (Litex.R (M := M)) h_3 (show @Eq M.Value _ _ from Eq.refl _) h_19)) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.addValue (show (Litex.denote _value_i1) = (Litex.denote _value_i3) from h_3) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          exact (And.intro h_3 (And.intro h_4 h_5))
        )
      )
  )

theorem h_89 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_102 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_103 : Litex.In _value_i5 (Litex.R (M := M))) (h_87 : Litex.Same _value_i4 _value_i5), Litex.Same _value_i5 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_102 _Host_i5 _rep_i5 _value_i5 h_103 h_87
          have h_88 : Litex.Same _value_i5 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (h_87).symm
                )
            )
          exact h_88
        )
      )
  )

theorem h_107 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_110 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_111 : Litex.In _value_i7 (Litex.R (M := M))) (h_105 : Litex.Same _value_i6 _value_i7), Litex.Same _value_i7 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_110 _Host_i7 _rep_i7 _value_i7 h_111 h_105
          exact ((h_89 (M := M)) _value_i6 h_110 _value_i7 h_111 h_105)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_transitivity_x2f_statement_x2e_lit
