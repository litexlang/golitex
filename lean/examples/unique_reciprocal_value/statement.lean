import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_reciprocal_x5f_value_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.RStar (M := M)) := (Litex.rStarNonempty (M := M))

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRStar_nonzero _value_i1 h_2)
      )
  )

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_6 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) (Litex.isSet (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)))
          have h_95 : Litex.In _value_i2 (Litex.R (M := M)) := (by
            let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
            exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.inRStar_base _value_i1 h_2) (_atomic_wd_1_0).wd.2.2))
          have h_96 : Litex.Same _value_i2 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) := rfl
          have h_97 : (by
            let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨⟨_value_i2, h_95, h_97⟩, (by
            intro _unique_left_i2 _member_left_i2 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0
            exact (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_127 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_128 : Litex.In _value_i4 (Litex.R (M := M))) (h_99 : (by
            let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
            exact Litex.Same _value_i3 _equal_wd_1_1)) (h_100 : (by
            let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
            exact Litex.Same _value_i4 _equal_wd_1_1)), Litex.Same _value_i3 _value_i4 from (by
            intro _Host_i3 _rep_i3 _value_i3 h_127 _Host_i4 _rep_i4 _value_i4 h_128 h_99 h_100
            have h_101 : Litex.Same _value_i3 _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    ((h_99).trans (h_100).symm)
                  )
              )
            exact h_101
          )) _unique_left_i2 _member_left_i2 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0)⟩
      )
  )

theorem h_133 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_membership_i6 : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)) (h_130 : ((Litex.denote _value_i5) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (h_131 : ((Litex.denote _value_i6) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), ((Litex.denote _value_i5) = (Litex.denote _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 _membership_i5 _Host_i6 _rep_i6 _value_i6 _membership_i6 h_130 h_131
          have _unique : ∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2) := ((h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) _membership_i5 (Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)) _membership_i6 h_130 h_131
          exact _same)
      )
  )

theorem h_135 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : (∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_136 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Same _value_i7 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i7 : Litex.Obj (M := M) M.Value) (_member_left_i7 : M.mem (Litex.denote _unique_left_i7) (M.standard Litex.StandardSetValue.real)) (_unique_right_i7 : Litex.Obj (M := M) M.Value) (_member_right_i7 : M.mem (Litex.denote _unique_right_i7) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i7) = (Litex.denote _unique_right_i7)) :=
  (by
    litex_complete =>
      exact (
        (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
      )
  )

theorem h_168 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) (h_165 : ((Litex.denote _value_i8) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (h_166 : ((Litex.denote _value_i9) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_165 h_166
          have _unique : ∀ (_unique_left_i7 : Litex.Obj (M := M) M.Value) (_member_left_i7 : M.mem (Litex.denote _unique_left_i7) (M.standard Litex.StandardSetValue.real)) (_unique_right_i7 : Litex.Obj (M := M) M.Value) (_member_right_i7 : M.mem (Litex.denote _unique_right_i7) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i7) = (Litex.denote _unique_right_i7) := ((h_135 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_165 h_166
          exact _same)
      )
  )

noncomputable def _value_i11 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_171 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) from (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).1)

theorem h_200 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : Litex.In (_value_i11 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_171 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) from (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).1))))
      )
  )

theorem h_201 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : Litex.Same (_value_i11 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_171 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) from (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).1))))
      )
  )

theorem h_205 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) (h_202 : ((Litex.denote _value_i12) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (h_203 : ((Litex.denote _value_i13) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), ((Litex.denote _value_i12) = (Litex.denote _value_i13)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 _membership_i12 _Host_i13 _rep_i13 _value_i13 _membership_i13 h_202 h_203
          have _unique : ∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10) := ((show (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_171 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) from (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) _membership_i12 (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) _membership_i13 h_202 h_203
          exact _same)
      )
  )

theorem h_206 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.RStar (M := M))) : (by
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 (Litex.inRStar_base _value_i1 h_2)) (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
  exact Litex.Same (_value_i11 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_201 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_reciprocal_x5f_value_x2f_statement_x2e_lit
