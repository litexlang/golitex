import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_reciprocal_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_7) h_1)) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 h_1
          have h_33 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_6 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_34 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)) (Litex.isSet (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1))
                    have h_106 : Litex.In _value_i3 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_33 (_atomic_wd_1_0).wd.2.2))
                    have h_107 : Litex.Same _value_i3 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1) := rfl
                    have h_108 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i3, h_106, h_108⟩, (by
                      intro _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_138 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_139 : Litex.In _value_i6 (Litex.R (M := M))) (h_110 : (by
                      let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact Litex.Same _value_i5 _equal_wd_1_1)) (h_111 : (by
                      let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact Litex.Same _value_i6 _equal_wd_1_1)), Litex.Same _value_i5 _value_i6 from (by
                      intro _Host_i5 _rep_i5 _value_i5 h_138 _Host_i6 _rep_i6 _value_i6 h_139 h_110 h_111
                      have h_112 : Litex.Same _value_i5 _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_110).trans (h_111).symm)
                            )
                        )
                      exact h_112
                    )) _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0)⟩
                )
            )

          have h_144 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_141 : ((Litex.denote _value_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (h_142 : ((Litex.denote _value_i8) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_141 h_142
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_6).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 h_141 h_142
                    exact _same)
                )
            )
          exact h_6
        )
      )
  )

theorem h_197 : (∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_198 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_213 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_214 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          rcases ((h_4 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_213 h_214) with ⟨_known_exists, _known_unique⟩
          rcases _known_exists with ⟨_value_i9, h_198, h_196⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) := (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))
          exact ⟨⟨_value_i9, h_198, h_196⟩, _known_unique⟩
        )
      )
  )

theorem h_218 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) (h_215 : ((Litex.denote _value_i10) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (h_216 : ((Litex.denote _value_i11) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), ((Litex.denote _value_i10) = (Litex.denote _value_i11)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i11 _rep_i11 _value_i11 _membership_i11 h_215 h_216
          have _unique : ∀ (_unique_left_i9 : Litex.Obj (M := M) M.Value) (_member_left_i9 : M.mem (Litex.denote _unique_left_i9) (M.standard Litex.StandardSetValue.real)) (_unique_right_i9 : Litex.Obj (M := M) M.Value) (_member_right_i9 : M.mem (Litex.denote _unique_right_i9) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i9) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i9) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i9) = (Litex.denote _unique_right_i9) := ((h_197 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 h_215 h_216
          exact _same)
      )
  )

noncomputable def _value_i13 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_221 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_197 (M := M)))).1)

theorem h_229 : Litex.In (_value_i13 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_221 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_197 (M := M)))).1))))
      )
  )

theorem h_230 : Litex.Same (_value_i13 (M := M)) ((fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_221 : Litex.In _value_i12 (Litex.R (M := M))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (_value_i13 (M := M)) (h_229 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_221 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_197 (M := M)))).1))))
      )
  )

theorem h_234 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) (h_231 : ((Litex.denote _value_i14) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (h_232 : ((Litex.denote _value_i15) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), ((Litex.denote _value_i14) = (Litex.denote _value_i15)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 _membership_i14 _Host_i15 _rep_i15 _value_i15 _membership_i15 h_231 h_232
          have _unique : ∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12) := ((show (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_221 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) from (h_197 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15 h_231 h_232
          exact _same)
      )
  )

theorem h_235 : (by
  let _equal_wd_1_1 := ((fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_221 : Litex.In _value_i12 (Litex.R (M := M))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (_value_i13 (M := M)) (h_229 (M := M)))
  exact Litex.Same (_value_i13 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_230 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_reciprocal_x2f_statement_x2e_lit
