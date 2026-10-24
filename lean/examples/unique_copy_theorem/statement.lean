import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_copy_x5f_theorem_x2f_statement_x2e_lit

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

theorem h_59 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_61 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_57 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          exact ((h_3 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_57)
        )
      )
  )

theorem h_65 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) (h_62 : ((Litex.denote _value_i9) = (M.number (2 : ℂ)))) (h_63 : ((Litex.denote _value_i10) = (M.number (2 : ℂ)))), ((Litex.denote _value_i9) = (Litex.denote _value_i10)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i10 _rep_i10 _value_i10 _membership_i10 h_62 h_63
          have _unique : ∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2) := ((h_59 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 h_62 h_63
          exact _same)
      )
  )

noncomputable def _value_i12 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_68 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11)) from (h_59 (M := M)))).1)

theorem h_69 : Litex.In (_value_i12 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_68 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11)) from (h_59 (M := M)))).1))))
      )
  )

theorem h_70 : Litex.Same (_value_i12 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_68 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11)) from (h_59 (M := M)))).1))))
      )
  )

theorem h_74 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) (h_71 : ((Litex.denote _value_i13) = (M.number (2 : ℂ)))) (h_72 : ((Litex.denote _value_i14) = (M.number (2 : ℂ)))), ((Litex.denote _value_i13) = (Litex.denote _value_i14)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i14 _rep_i14 _value_i14 _membership_i14 h_71 h_72
          have _unique : ∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11) := ((show (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_68 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (2 : ℂ)))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11)) from (h_59 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) _membership_i13 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 h_71 h_72
          exact _same)
      )
  )

theorem h_75 : Litex.Same (_value_i12 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_70 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_copy_x5f_theorem_x2f_statement_x2e_lit
