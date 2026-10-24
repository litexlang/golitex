import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_copy_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i1) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          have h_8 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_5 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_9 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 _value_i1) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)
                    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_8
                    have h_16 : Litex.Same _value_i3 _value_i1 := rfl
                    have h_17 : Litex.Same _value_i1 _value_i1 := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i3, h_15, h_17⟩, (by
                      intro _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_47 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_48 : Litex.In _value_i6 (Litex.R (M := M))) (h_19 : Litex.Same _value_i5 _value_i1) (h_20 : Litex.Same _value_i6 _value_i1), Litex.Same _value_i5 _value_i6 from (by
                      intro _Host_i5 _rep_i5 _value_i5 h_47 _Host_i6 _rep_i6 _value_i6 h_48 h_19 h_20
                      have h_21 : Litex.Same _value_i5 _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_19).trans (h_20).symm)
                            )
                        )
                      exact h_21
                    )) _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0)⟩
                )
            )

          have h_53 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_50 : ((Litex.denote _value_i7) = (Litex.denote _value_i1))) (h_51 : ((Litex.denote _value_i8) = (Litex.denote _value_i1))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_50 h_51
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_5).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 h_50 h_51
                    exact _same)
                )
            )
          exact h_5
        )
      )
  )

theorem h_58 : (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_59 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_65 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          rcases ((h_3 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_65) with ⟨_known_exists, _known_unique⟩
          rcases _known_exists with ⟨_value_i9, h_59, h_57⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))
          exact ⟨⟨_value_i9, h_59, h_57⟩, _known_unique⟩
        )
      )
  )

theorem h_69 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) (h_66 : ((Litex.denote _value_i10) = (M.number (3 : ℂ)))) (h_67 : ((Litex.denote _value_i11) = (M.number (3 : ℂ)))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11 h_66 h_67
          have _unique : ∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9) := ((h_58 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 h_66 h_67
          exact _same)
      )
  )

noncomputable def _value_i13 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_72 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_58 (M := M)))).1)

theorem h_73 : Litex.In (_value_i13 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_72 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_58 (M := M)))).1))))
      )
  )

theorem h_74 : Litex.Same (_value_i13 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_72 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_58 (M := M)))).1))))
      )
  )

theorem h_78 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) (h_75 : ((Litex.denote _value_i14) = (M.number (3 : ℂ)))) (h_76 : ((Litex.denote _value_i15) = (M.number (3 : ℂ)))), ((Litex.denote _value_i14) = (Litex.denote _value_i15)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 _membership_i14 _Host_i15 _rep_i15 _value_i15 _membership_i15 h_75 h_76
          have _unique : ∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12) := ((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_72 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (3 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (3 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_58 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15 h_75 h_76
          exact _same)
      )
  )

theorem h_79 : Litex.Same (_value_i13 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_74 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_copy_x2f_statement_x2e_lit
