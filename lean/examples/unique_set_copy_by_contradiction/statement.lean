import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_set_x5f_copy_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.IsSet _value_i1), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.IsSet _value_i2), Litex.Same _value_i2 _value_i1) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.isSet (Litex.denote _unique_left_i2)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.isSet (Litex.denote _unique_right_i2)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10
          have h_12 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_5 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.IsSet _value_i3), Litex.Same _value_i3 _value_i1) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.isSet (Litex.denote _unique_left_i3)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.isSet (Litex.denote _unique_right_i3)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_17 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_18 : Litex.IsSet _value_i3) (h_4 : Litex.Same _value_i3 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.IsSet _value_i7), ∃ (h_15 : Litex.Same _value_i7 _value_i1), ¬ Litex.Same _value_i7 _value_i3 := (by
                      classical
                      intro _value_i3 h_18 h_4
                      apply Classical.byContradiction
                      intro _no_alternative
                      apply _litex_negated_goal
                      constructor
                      · exact ⟨(Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)), h_18, h_4⟩
                      · intro _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0
                        have _same_left_i3 : Litex.denote _unique_left_i3 = Litex.denote _value_i3 := by
                          apply Classical.byContradiction
                          intro _different
                          apply _no_alternative
                          exact ⟨_unique_left_i3, _member_left_i3, _body_left_0, _different⟩
                        have _same_right_i3 : Litex.denote _unique_right_i3 = Litex.denote _value_i3 := by
                          apply Classical.byContradiction
                          intro _different
                          apply _no_alternative
                          exact ⟨_unique_right_i3, _member_right_i3, _body_right_0, _different⟩
                        simp only [_same_left_i3, _same_right_i3])
                    rcases (show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_20 : Litex.IsSet _value_i4), ∃ (h_6 : Litex.Same _value_i4 _value_i1), ¬ Litex.Same _value_i4 _value_i1 from (by
                      have h_28 : Litex.IsSet _value_i1 :=
                        h_12
                      have h_31 : Litex.Same _value_i1 _value_i1 :=
                        (show @Eq M.Value _ _ from Eq.refl _)
                      rcases ((show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.IsSet _value_i3) (h_4 : Litex.Same _value_i3 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.IsSet _value_i7), ∃ (h_15 : Litex.Same _value_i7 _value_i1), ¬ Litex.Same _value_i7 _value_i3 from (fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.IsSet _value_i3) (h_4 : Litex.Same _value_i3 _value_i1) => by
                        exact h_17 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_18 h_4)) _value_i1 h_28 h_31) with ⟨_value_i4, h_20, h_6, h_7⟩
                      have _exist_match_0 : Litex.Same _value_i1 _value_i1 := (Litex.sameRefl _value_i1)
                      have _exist_match_1 : Litex.Same _value_i1 _value_i1 := (Litex.sameRefl _value_i1)
                      exact ⟨_value_i4, h_20, h_6, h_7⟩
                    )) with ⟨_value_i5, h_33, h_34, h_35⟩
                    exact (by
                      have _asserted : Litex.Same _value_i5 _value_i1 := h_34
                      have _denied : ¬ (Litex.Same _value_i5 _value_i1) := h_35
                      exact _denied _asserted)
                  )
                )
            )

          have h_46 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.isSet (Litex.denote _value_i8)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.isSet (Litex.denote _value_i9)) (h_43 : ((Litex.denote _value_i8) = (Litex.denote _value_i1))) (h_44 : ((Litex.denote _value_i9) = (Litex.denote _value_i1))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_43 h_44
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.isSet (Litex.denote _unique_left_i3)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.isSet (Litex.denote _unique_right_i3)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_5).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_43 h_44
                    exact _same)
                )
            )
          exact h_5
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_set_x5f_copy_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
