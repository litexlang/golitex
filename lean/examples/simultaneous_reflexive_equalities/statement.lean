import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_simultaneous_x5f_reflexive_x5f_equalities_x2f_statement_x2e_lit

universe u v1 v2 v4 v6 v8 v10 v11
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (Litex.R (M := M))), ((Litex.Same _value_i1 _value_i1) ∧ (Litex.Same _value_i2 _value_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12
          have h_13 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_14 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_7 : ((Litex.Same _value_i1 _value_i1) ∧ (Litex.Same _value_i2 _value_i2)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_17 : ((¬ Litex.Same _value_i1 _value_i1) ∨ (¬ Litex.Same _value_i2 _value_i2)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    exact (by
                      have _asserted : (Litex.Same _value_i1 _value_i1) ∧ (Litex.Same _value_i2 _value_i2) := (And.intro (show @Eq M.Value _ _ from Eq.refl _) (show @Eq M.Value _ _ from Eq.refl _))
                      have _denied : ¬ ((Litex.Same _value_i1 _value_i1) ∧ (Litex.Same _value_i2 _value_i2)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show ((¬ Litex.Same _value_i1 _value_i1) ∨ (¬ Litex.Same _value_i2 _value_i2)) from h_17))
                      exact _denied _asserted)
                  )
                )
            )

          have h_5 :=
            (And.left h_7)

          have h_6 :=
            (And.right h_7)
          exact (And.intro (show @Eq M.Value _ _ from Eq.refl _) (show @Eq M.Value _ _ from Eq.refl _))
        )
      )
  )

theorem h_78 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_85 : Litex.In _value_i4 (Litex.R (M := M))), ((Litex.Same _value_i4 _value_i4) ∨ (¬ Litex.Same _value_i4 _value_i4)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_85
          have h_86 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_85
                )
            )
          have h_81 : ((Litex.Same _value_i4 _value_i4) ∨ (¬ Litex.Same _value_i4 _value_i4)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_89 : ((¬ Litex.Same _value_i4 _value_i4) ∧ (Litex.Same _value_i4 _value_i4)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    have h_87 :=
                      (And.left h_89)
                    have h_88 :=
                      (And.right h_89)
                    exact (by
                      have _asserted : ((Litex.Same _value_i4 _value_i4) ∨ (¬ Litex.Same _value_i4 _value_i4)) := (Classical.em (Litex.Same _value_i4 _value_i4))
                      have _denied : ¬ (((Litex.Same _value_i4 _value_i4) ∨ (¬ Litex.Same _value_i4 _value_i4))) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show (¬ Litex.Same _value_i4 _value_i4) ∧ (Litex.Same _value_i4 _value_i4) from (And.intro h_87 (show @Eq M.Value _ _ from Eq.refl _))))
                      exact _denied _asserted)
                  )
                )
            )
          exact (Classical.em (Litex.Same _value_i4 _value_i4))
        )
      )
  )

theorem h_102 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_105 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Same _value_i6 _value_i6) ∧ (Litex.Same _value_i6 _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_105
          have h_108 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_105
                )
            )
          have h_103 : ((Litex.Same _value_i6 _value_i6) ∧ (Litex.Same _value_i6 _value_i6)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_115 : ((¬ Litex.Same _value_i6 _value_i6) ∨ (¬ Litex.Same _value_i6 _value_i6)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    exact (by
                      have _asserted : (Litex.Same _value_i6 _value_i6) ∧ (Litex.Same _value_i6 _value_i6) := (And.intro (show @Eq M.Value _ _ from Eq.refl _) (show @Eq M.Value _ _ from Eq.refl _))
                      have _denied : ¬ ((Litex.Same _value_i6 _value_i6) ∧ (Litex.Same _value_i6 _value_i6)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show ((¬ Litex.Same _value_i6 _value_i6) ∨ (¬ Litex.Same _value_i6 _value_i6)) from h_115))
                      exact _denied _asserted)
                  )
                )
            )

          have h_171 :=
            (And.left h_103)

          have h_172 :=
            (And.right h_103)

          have h_173 :=
            h_171

          have h_174 :=
            h_172

          have h_175 :=
            (Eq.trans h_171 h_172)
          exact (And.intro (show @Eq M.Value _ _ from Eq.refl _) (show @Eq M.Value _ _ from Eq.refl _))
        )
      )
  )

theorem h_190 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_205 : Litex.In _value_i8 (Litex.R (M := M))), ((((Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (¬ Litex.Same _value_i8 _value_i8)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_205
          have h_206 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_205
                )
            )
          have h_197 : ((((Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (¬ Litex.Same _value_i8 _value_i8)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_215 : ((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8)))))))) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    exact (by
                      have _asserted : ((((Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (¬ Litex.Same _value_i8 _value_i8)))) := (Or.inl (by
                      have h_220 : Litex.In _value_i8 (Litex.R (M := M)) :=
                        h_206
                      have h_225 : Litex.In _value_i8 (Litex.R (M := M)) :=
                        h_206
                      exact (And.intro (Eq.trans (Eq.symm (Litex.sameRefl _value_i8)) (Eq.trans (And.left ((h_4 (M := M)) _value_i8 h_220 _value_i8 h_225)) (Litex.sameRefl _value_i8))) (Eq.trans (Eq.symm (Litex.sameRefl _value_i8)) (Eq.trans (And.right ((h_4 (M := M)) _value_i8 h_220 _value_i8 h_225)) (Litex.sameRefl _value_i8))))
                    ))
                      have _denied : ¬ (((((Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (¬ Litex.Same _value_i8 _value_i8))))) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show ((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8))) ∨ (((¬ Litex.Same _value_i8 _value_i8) ∧ (Litex.Same _value_i8 _value_i8)))))))) from h_215))
                      exact _denied _asserted)
                  )
                )
            )
          exact (Or.inl (by
            have h_335 : Litex.In _value_i8 (Litex.R (M := M)) :=
              h_206
            have h_340 : Litex.In _value_i8 (Litex.R (M := M)) :=
              h_206
            exact (And.intro (Eq.trans (Eq.symm (Litex.sameRefl _value_i8)) (Eq.trans (And.left ((h_4 (M := M)) _value_i8 h_335 _value_i8 h_340)) (Litex.sameRefl _value_i8))) (Eq.trans (Eq.symm (Litex.sameRefl _value_i8)) (Eq.trans (And.right ((h_4 (M := M)) _value_i8 h_335 _value_i8 h_340)) (Litex.sameRefl _value_i8))))
          ))
        )
      )
  )

theorem h_349 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_356 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_357 : Litex.In _value_i11 (Litex.R (M := M))), ((Litex.Le _value_i10 _value_i10) ∧ (Litex.Le _value_i11 _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_356 _Host_i11 _rep_i11 _value_i11 h_357
          have h_382 : Litex.In _value_i10 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_356
                )
            )
          have h_383 : Litex.In _value_i11 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_357
                )
            )
          have h_352 : ((Litex.Le _value_i10 _value_i10) ∧ (Litex.Le _value_i11 _value_i11)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_410 : ((¬ Litex.Le _value_i10 _value_i10) ∨ (¬ Litex.Le _value_i11 _value_i11)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    exact (by
                      have _asserted : (Litex.Le _value_i10 _value_i10) ∧ (Litex.Le _value_i11 _value_i11) := (And.intro (Litex.leRefl _value_i10 h_382) (Litex.leRefl _value_i11 h_383))
                      have _denied : ¬ ((Litex.Le _value_i10 _value_i10) ∧ (Litex.Le _value_i11 _value_i11)) := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show ((¬ Litex.Le _value_i10 _value_i10) ∨ (¬ Litex.Le _value_i11 _value_i11)) from h_410))
                      exact _denied _asserted)
                  )
                )
            )

          have h_350 :=
            (And.left h_352)

          have h_351 :=
            (And.right h_352)
          exact (And.intro h_350 h_351)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_simultaneous_x5f_reflexive_x5f_equalities_x2f_statement_x2e_lit
