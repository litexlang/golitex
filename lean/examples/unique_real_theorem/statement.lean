import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_theorem_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_2 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4 : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_6 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
                    have h_8 : Litex.In _value_i2 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                    have h_9 : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := rfl
                    have h_10 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i2, h_8, h_10⟩, (by
                      intro _unique_left_i2 _member_left_i2 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_40 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_41 : Litex.In _value_i5 (Litex.R (M := M))) (h_12 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_13 : Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i4 _value_i5 from (by
                      intro _Host_i4 _rep_i4 _value_i4 h_40 _Host_i5 _rep_i5 _value_i5 h_41 h_12 h_13
                      have h_14 : Litex.Same _value_i4 _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_12).trans (h_13).symm)
                            )
                        )
                      exact h_14
                    )) _unique_left_i2 _member_left_i2 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0)⟩
                )
            )

          have h_46 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_membership_i6 : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) (h_43 : ((Litex.denote _value_i6) = (M.number (0 : ℂ)))) (h_44 : ((Litex.denote _value_i7) = (M.number (0 : ℂ)))), ((Litex.denote _value_i6) = (Litex.denote _value_i7)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i6 _rep_i6 _value_i6 _membership_i6 _Host_i7 _rep_i7 _value_i7 _membership_i7 h_43 h_44
                    have _unique : ∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2) := (h_4).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)) _membership_i6 (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 h_43 h_44
                    exact _same)
                )
            )
          exact h_4
        )
      )
  )

theorem h_52 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) (h_49 : ((Litex.denote _value_i8) = (M.number (0 : ℂ)))) (h_50 : ((Litex.denote _value_i9) = (M.number (0 : ℂ)))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_49 h_50
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_49 h_50
          exact _same)
      )
  )

theorem h_58 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) (h_55 : ((Litex.denote _value_i10) = (M.number (0 : ℂ)))) (h_56 : ((Litex.denote _value_i11) = (M.number (0 : ℂ)))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11 h_55 h_56
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 h_55 h_56
          exact _same)
      )
  )

theorem h_60 : (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_61 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_67 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) (h_64 : ((Litex.denote _value_i13) = (M.number (0 : ℂ)))) (h_65 : ((Litex.denote _value_i14) = (M.number (0 : ℂ)))), ((Litex.denote _value_i13) = (Litex.denote _value_i14)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i14 _rep_i14 _value_i14 _membership_i14 h_64 h_65
                    have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_2 (M := M))).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) _membership_i13 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 h_64 h_65
                    exact _same)
                )
            )
          exact (h_2 (M := M))
        )
      )
  )

theorem h_73 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_membership_i16 : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)) (h_70 : ((Litex.denote _value_i15) = (M.number (0 : ℂ)))) (h_71 : ((Litex.denote _value_i16) = (M.number (0 : ℂ)))), ((Litex.denote _value_i15) = (Litex.denote _value_i16)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 _membership_i15 _Host_i16 _rep_i16 _value_i16 _membership_i16 h_70 h_71
          have _unique : ∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12) := ((h_60 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15 (Litex.semanticObject (Litex.denote _value_i16) (Litex.isSet _value_i16)) _membership_i16 h_70 h_71
          exact _same)
      )
  )

noncomputable def _value_i18 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i17) = (Litex.denote _unique_right_i17)) from (h_2 (M := M)))).1)

theorem h_77 : Litex.In (_value_i18 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i17) = (Litex.denote _unique_right_i17)) from (h_2 (M := M)))).1))))
      )
  )

theorem h_78 : Litex.Same (_value_i18 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i17) = (Litex.denote _unique_right_i17)) from (h_2 (M := M)))).1))))
      )
  )

theorem h_82 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_membership_i19 : M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (_membership_i20 : M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)) (h_79 : ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) (h_80 : ((Litex.denote _value_i20) = (M.number (0 : ℂ)))), ((Litex.denote _value_i19) = (Litex.denote _value_i20)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 _membership_i19 _Host_i20 _rep_i20 _value_i20 _membership_i20 h_79 h_80
          have _unique : ∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i17) = (Litex.denote _unique_right_i17) := ((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_76 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (0 : ℂ)))), (Litex.denote _unique_left_i17) = (Litex.denote _unique_right_i17)) from (h_2 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i19) (Litex.isSet _value_i19)) _membership_i19 (Litex.semanticObject (Litex.denote _value_i20) (Litex.isSet _value_i20)) _membership_i20 h_79 h_80
          exact _same)
      )
  )

theorem h_83 : Litex.Same (_value_i18 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_78 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_theorem_x2f_statement_x2e_lit
