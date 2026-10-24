import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_membership_x5f_distinguishes_x5f_sets_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v10 v11 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.IsSet _value_i3) (h_1 : Litex.In _value_i3 _value_i1) (h_2 : ¬ Litex.In _value_i3 _value_i2), ¬ Litex.Same _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_9 h_1 h_2
          have h_10 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_11 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_12 : Litex.IsSet _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_5 : ¬ Litex.Same _value_i1 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_13 : Litex.Same _value_i1 _value_i2 := Classical.byContradiction _litex_negated_goal
                    exact (by
                      have _asserted : Litex.In _value_i3 _value_i2 := (Litex.inOfSame _value_i3 _value_i3 _value_i1 _value_i2 (show @Eq M.Value _ _ from Eq.refl _) h_13 h_1)
                      have _denied : ¬ (Litex.In _value_i3 _value_i2) := h_2
                      exact _denied _asserted)
                  )
                )
            )
          exact h_5
        )
      )
  )

theorem h_33 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_36 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_37 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_38 : Litex.IsSet _value_i7) (h_30 : Litex.In _value_i7 _value_i5) (h_31 : ¬ Litex.In _value_i7 _value_i6), ¬ Litex.Subset _value_i5 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_36 _Host_i6 _rep_i6 _value_i6 h_37 _Host_i7 _rep_i7 _value_i7 h_38 h_30 h_31
          have h_39 : Litex.IsSet _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_36
                )
            )
          have h_40 : Litex.IsSet _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_37
                )
            )
          have h_41 : Litex.IsSet _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  h_38
                )
            )
          have h_34 : ¬ Litex.Subset _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_42 : Litex.Subset _value_i5 _value_i6 := Classical.byContradiction _litex_negated_goal
                    exact (by
                      have _asserted : Litex.In _value_i7 _value_i6 := (h_42 (Litex.denote _value_i7) h_30)
                      have _denied : ¬ (Litex.In _value_i7 _value_i6) := h_31
                      exact _denied _asserted)
                  )
                )
            )
          exact h_34
        )
      )
  )

theorem h_76 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_82 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_83 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_84 : Litex.IsSet _value_i12) (h_73 : (by
  let _atomic_wd_1_1 := (Litex.union _value_i10 _value_i11)
  exact Litex.In _value_i12 _atomic_wd_1_1)) (h_74 : ¬ Litex.In _value_i12 _value_i10), Litex.In _value_i12 _value_i11 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_82 _Host_i11 _rep_i11 _value_i11 h_83 _Host_i12 _rep_i12 _value_i12 h_84 h_73 h_74
          have h_87 : ((Litex.In _value_i12 _value_i10) ∨ (Litex.In _value_i12 _value_i11)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inUnion_iff _value_i12 _value_i10 _value_i11).mp h_73)
                )
            )
          have h_90 : Litex.IsSet _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  h_82
                )
            )
          have h_91 : Litex.IsSet _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  h_83
                )
            )
          have h_92 : Litex.IsSet _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  h_84
                )
            )
          have h_95 : ((Litex.In _value_i12 _value_i10) ∨ (Litex.In _value_i12 _value_i11)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inUnion_iff _value_i12 _value_i10 _value_i11).mp h_73)
                )
            )
          have _cases_result_98 : Litex.In _value_i12 _value_i11 :=
            ((fun _litex_cases_tail => Or.elim _litex_cases_tail (fun (h_78 : Litex.In _value_i12 _value_i10) => by
            exact False.elim (by
              have _asserted : Litex.In _value_i12 _value_i10 := h_78
              have _denied : ¬ (Litex.In _value_i12 _value_i10) := h_74
              exact _denied _asserted)
          ) (fun (h_80 : Litex.In _value_i12 _value_i11) => by
            have h_81 : Litex.In _value_i12 _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    h_80
                  )
              )
            have h_77 : Litex.In _value_i12 _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    h_80
                  )
              )
            exact h_77
          )) h_95)

          have h_77 : Litex.In _value_i12 _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  _cases_result_98
                )
            )
          exact h_77
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_membership_x5f_distinguishes_x5f_sets_x2f_statement_x2e_lit
