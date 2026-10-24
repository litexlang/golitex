import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_incompatible_x5f_existential_x5f_equalities_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_3 : ¬ (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_12 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i1 _value_i2), ¬ Litex.Same _value_i1 _value_i2) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_6 : ¬ (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_14 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_4 : Litex.Same _value_i3 _value_i4), ¬ Litex.Same _value_i3 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    apply Classical.byContradiction
                    intro _litex_negated_goal
                    have h_15 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_16 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_17 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_4 : Litex.Same _value_i3 _value_i4), ¬ Litex.Same _value_i3 _value_i4 := (by
                      classical
                      simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
                    rcases (show ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_18 : Litex.In _value_i5 (Litex.R (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i6 (Litex.R (M := M))), ∃ (h_7 : Litex.Same _value_i5 _value_i6), ¬ Litex.Same _value_i5 _value_i6 from h_15) with ⟨_value_i7, h_20, _value_i8, h_21, h_22, h_23⟩
                    exact (by
                      have _asserted : Litex.Same _value_i7 _value_i8 := h_22
                      have _denied : ¬ (Litex.Same _value_i7 _value_i8) := h_23
                      exact _denied _asserted)
                  )
                )
            )

          have h_37 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i10) = (Litex.denote _value_i11)))) ∨ (((Litex.denote _value_i10) = (Litex.denote _value_i11)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11
                    have _excluded : ¬ ((∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)), ∃ (h_4 : ((Litex.denote _value_i3) = (Litex.denote _value_i4))), (¬ ((Litex.denote _value_i3) = (Litex.denote _value_i4))))) := h_6
                    have _no_body : ¬ (((((Litex.denote _value_i10) = (Litex.denote _value_i11))) ∧ ((¬ ((Litex.denote _value_i10) = (Litex.denote _value_i11)))))) := by
                      intro _candidate
                      rcases _candidate with ⟨h_4, h_5⟩
                      apply _excluded
                      exact ⟨Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10), _membership_i10, Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11), _membership_i11, h_4, h_5⟩
                    simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
                )
            )
          exact h_6
        )
      )
  )

theorem h_47 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i12) = (Litex.denote _value_i13)))) ∨ (((Litex.denote _value_i12) = (Litex.denote _value_i13)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i12 _rep_i12 _value_i12 _membership_i12 _Host_i13 _rep_i13 _value_i13 _membership_i13
          have _excluded : ¬ ((∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : ((Litex.denote _value_i1) = (Litex.denote _value_i2))), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i2))))) := (h_3 (M := M))
          have _no_body : ¬ (((((Litex.denote _value_i12) = (Litex.denote _value_i13))) ∧ ((¬ ((Litex.denote _value_i12) = (Litex.denote _value_i13)))))) := by
            intro _candidate
            rcases _candidate with ⟨h_1, h_2⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12), _membership_i12, Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13), _membership_i13, h_1, h_2⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )

theorem h_57 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i14) = (Litex.denote _value_i15)))) ∨ (((Litex.denote _value_i14) = (Litex.denote _value_i15)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i14 _rep_i14 _value_i14 _membership_i14 _Host_i15 _rep_i15 _value_i15 _membership_i15
          have _excluded : ¬ ((∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : ((Litex.denote _value_i1) = (Litex.denote _value_i2))), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i2))))) := (h_3 (M := M))
          have _no_body : ¬ (((((Litex.denote _value_i14) = (Litex.denote _value_i15))) ∧ ((¬ ((Litex.denote _value_i14) = (Litex.denote _value_i15)))))) := by
            intro _candidate
            rcases _candidate with ⟨h_1, h_2⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14), _membership_i14, Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15), _membership_i15, h_1, h_2⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )

theorem h_60 : ¬ (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_61 : Litex.In _value_i16 (Litex.R (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_62 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (h_58 : Litex.Same _value_i16 _value_i17), ¬ Litex.Same _value_i16 _value_i17) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_72 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (_membership_i18 : M.mem (Litex.denote _value_i18) (M.standard Litex.StandardSetValue.real)) {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_membership_i19 : M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i18) = (Litex.denote _value_i19)))) ∨ (((Litex.denote _value_i18) = (Litex.denote _value_i19)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    intro _Host_i18 _rep_i18 _value_i18 _membership_i18 _Host_i19 _rep_i19 _value_i19 _membership_i19
                    have _excluded : ¬ ((∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : ((Litex.denote _value_i1) = (Litex.denote _value_i2))), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i2))))) := (h_3 (M := M))
                    have _no_body : ¬ (((((Litex.denote _value_i18) = (Litex.denote _value_i19))) ∧ ((¬ ((Litex.denote _value_i18) = (Litex.denote _value_i19)))))) := by
                      intro _candidate
                      rcases _candidate with ⟨h_1, h_2⟩
                      apply _excluded
                      exact ⟨Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18), _membership_i18, Litex.semanticObject (Litex.denote _value_i19) (Litex.isSet _value_i19), _membership_i19, h_1, h_2⟩
                    simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
                )
            )
          exact (h_3 (M := M))
        )
      )
  )

theorem h_82 : ∀ {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (_membership_i20 : M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)) {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (_membership_i21 : M.mem (Litex.denote _value_i21) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i20) = (Litex.denote _value_i21)))) ∨ (((Litex.denote _value_i20) = (Litex.denote _value_i21)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i20 _rep_i20 _value_i20 _membership_i20 _Host_i21 _rep_i21 _value_i21 _membership_i21
          have _excluded : ¬ ((∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i17) (M.standard Litex.StandardSetValue.real)), ∃ (h_58 : ((Litex.denote _value_i16) = (Litex.denote _value_i17))), (¬ ((Litex.denote _value_i16) = (Litex.denote _value_i17))))) := (h_60 (M := M))
          have _no_body : ¬ (((((Litex.denote _value_i20) = (Litex.denote _value_i21))) ∧ ((¬ ((Litex.denote _value_i20) = (Litex.denote _value_i21)))))) := by
            intro _candidate
            rcases _candidate with ⟨h_58, h_59⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i20) (Litex.isSet _value_i20), _membership_i20, Litex.semanticObject (Litex.denote _value_i21) (Litex.isSet _value_i21), _membership_i21, h_58, h_59⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )

theorem h_85 : ¬ (∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_86 : Litex.In _value_i22 (Litex.R (M := M))), ∃ (_value_i23 : Litex.Obj (M := M) M.Value), ∃ (h_87 : Litex.In _value_i23 (Litex.R (M := M))), ∃ (h_83 : Litex.Same _value_i22 _value_i23), ¬ Litex.Same _value_i22 _value_i23) :=
  (by
    litex_complete =>
      exact (
        (h_3 (M := M))
      )
  )

theorem h_93 : ∀ {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_membership_i24 : M.mem (Litex.denote _value_i24) (M.standard Litex.StandardSetValue.real)) {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_membership_i25 : M.mem (Litex.denote _value_i25) (M.standard Litex.StandardSetValue.real)), (((¬ ((Litex.denote _value_i24) = (Litex.denote _value_i25)))) ∨ (((Litex.denote _value_i24) = (Litex.denote _value_i25)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i24 _rep_i24 _value_i24 _membership_i24 _Host_i25 _rep_i25 _value_i25 _membership_i25
          have _excluded : ¬ ((∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i22) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i23 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)), ∃ (h_83 : ((Litex.denote _value_i22) = (Litex.denote _value_i23))), (¬ ((Litex.denote _value_i22) = (Litex.denote _value_i23))))) := (h_85 (M := M))
          have _no_body : ¬ (((((Litex.denote _value_i24) = (Litex.denote _value_i25))) ∧ ((¬ ((Litex.denote _value_i24) = (Litex.denote _value_i25)))))) := by
            intro _candidate
            rcases _candidate with ⟨h_83, h_84⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i24) (Litex.isSet _value_i24), _membership_i24, Litex.semanticObject (Litex.denote _value_i25) (Litex.isSet _value_i25), _membership_i25, h_83, h_84⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_incompatible_x5f_existential_x5f_equalities_x2f_statement_x2e_lit
