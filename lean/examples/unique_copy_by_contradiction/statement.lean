import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_copy_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.R (M := M))), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i1) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10
          have h_12 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_5 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 _value_i1) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_17 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_4 : Litex.Same _value_i3 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (h_15 : Litex.Same _value_i7 _value_i1), ¬ Litex.Same _value_i7 _value_i3 := (by
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
                    rcases (show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_20 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_6 : Litex.Same _value_i4 _value_i1), ¬ Litex.Same _value_i4 _value_i1 from (by
                      have h_30 : Litex.In _value_i1 (Litex.R (M := M)) :=
                        h_12
                      have h_35 : Litex.Same _value_i1 _value_i1 :=
                        (show @Eq M.Value _ _ from Eq.refl _)
                      rcases ((show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_4 : Litex.Same _value_i3 _value_i1), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (h_15 : Litex.Same _value_i7 _value_i1), ¬ Litex.Same _value_i7 _value_i3 from (fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_4 : Litex.Same _value_i3 _value_i1) => by
                        exact h_17 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_18 h_4)) _value_i1 h_30 h_35) with ⟨_value_i4, h_20, h_6, h_7⟩
                      have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
                      have _exist_match_1 : Litex.Same _value_i1 _value_i1 := (Litex.sameRefl _value_i1)
                      have _exist_match_2 : Litex.Same _value_i1 _value_i1 := (Litex.sameRefl _value_i1)
                      exact ⟨_value_i4, h_20, h_6, h_7⟩
                    )) with ⟨_value_i5, h_37, h_38, h_39⟩
                    exact (by
                      have _asserted : Litex.Same _value_i5 _value_i1 := h_38
                      have _denied : ¬ (Litex.Same _value_i5 _value_i1) := h_39
                      exact _denied _asserted)
                  )
                )
            )

          have h_50 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) (h_47 : ((Litex.denote _value_i8) = (Litex.denote _value_i1))) (h_48 : ((Litex.denote _value_i9) = (Litex.denote _value_i1))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_47 h_48
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_5).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_47 h_48
                    exact _same)
                )
            )
          exact h_5
        )
      )
  )

theorem h_56 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_58 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_54 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          exact ((h_3 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_54)
        )
      )
  )

theorem h_62 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) (h_59 : ((Litex.denote _value_i10) = (M.number (3 : ℂ)))) (h_60 : ((Litex.denote _value_i11) = (M.number (3 : ℂ)))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11 h_59 h_60
          have _unique : ∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2) := ((h_56 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 h_59 h_60
          exact _same)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_copy_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
