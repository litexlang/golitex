import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_zero_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_2 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_3 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_5 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_6 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_7 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨⟨_value_i1, h_5, h_7⟩, (by
            intro _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0
            exact (show ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_37 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_38 : Litex.In _value_i3 (Litex.R (M := M))) (h_9 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) (h_10 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i2 _value_i3 from (by
            intro _Host_i2 _rep_i2 _value_i2 h_37 _Host_i3 _rep_i3 _value_i3 h_38 h_9 h_10
            have h_11 : Litex.Same _value_i2 _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    ((h_9).trans (h_10).symm)
                  )
              )
            exact h_11
          )) _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0)⟩
      )
  )

theorem h_43 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_membership_i4 : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)) (h_40 : ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) (h_41 : ((Litex.denote _value_i5) = (M.number (0 : ℂ)))), ((Litex.denote _value_i4) = (Litex.denote _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 _membership_i4 _Host_i5 _rep_i5 _value_i5 _membership_i5 h_40 h_41
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i4) (Litex.isSet _value_i4)) _membership_i4 (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) _membership_i5 h_40 h_41
          exact _same)
      )
  )

theorem h_45 : (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_46 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (M.standard Litex.StandardSetValue.real)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i6) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i6) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6)) :=
  (by
    litex_complete =>
      exact (
        (h_2 (M := M))
      )
  )

theorem h_50 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_47 : ((Litex.denote _value_i7) = (M.number (0 : ℂ)))) (h_48 : ((Litex.denote _value_i8) = (M.number (0 : ℂ)))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_47 h_48
          have _unique : ∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (M.standard Litex.StandardSetValue.real)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i6) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i6) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6) := ((h_45 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 h_47 h_48
          exact _same)
      )
  )

noncomputable def _value_i10 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_53 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) from (h_2 (M := M)))).1)

theorem h_54 : Litex.In (_value_i10 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_53 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) from (h_2 (M := M)))).1))))
      )
  )

theorem h_55 : Litex.Same (_value_i10 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_53 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) from (h_2 (M := M)))).1))))
      )
  )

theorem h_59 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) (h_56 : ((Litex.denote _value_i11) = (M.number (0 : ℂ)))) (h_57 : ((Litex.denote _value_i12) = (M.number (0 : ℂ)))), ((Litex.denote _value_i11) = (Litex.denote _value_i12)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 _membership_i11 _Host_i12 _rep_i12 _value_i12 _membership_i12 h_56 h_57
          have _unique : ∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9) := ((show (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_53 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) from (h_2 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) _membership_i12 h_56 h_57
          exact _same)
      )
  )

theorem h_60 : Litex.Same (_value_i10 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_55 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_zero_x2f_statement_x2e_lit
