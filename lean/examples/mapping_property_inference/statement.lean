import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_mapping_x5f_property_x5f_inference_x2f_statement_x2e_lit

universe u v1 v3 v4 v9 v11 v17 v18 v19
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_36 : Litex.In _value_i1 (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_35 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
    have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_37 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_38 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote _value_i1))) (h_2 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i3 h_36 h_37 True.intro)
  let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i4 h_36 h_38 True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_36 _Host_i3 _rep_i3 _value_i3 h_37 _Host_i4 _rep_i4 _value_i4 h_38 h_1 h_2
          have h_51 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_52 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i7)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i8)))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_52
                    exact h_1 (Litex.denote _value_i7) _membership_i7 (Litex.denote _value_i8) _membership_i8 h_52)
                )
            )
          have h_3 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_78 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      h_37
                    have h_85 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      h_38
                    have h_94 : (by
                      let _equal_wd_2_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i3 h_36 h_37 True.intro)
                      let _equal_wd_2_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i4 h_36 h_38 True.intro)
                      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
                      h_2
                    exact (Eq.trans (Eq.symm (Litex.sameRefl _value_i3)) (Eq.trans (h_51 _value_i3 h_78 _value_i4 h_85 h_94) (Litex.sameRefl _value_i4)))
                  )
                )
            )
          exact h_3
        )
      )
  )

theorem h_99 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_131 : Litex.In _value_i9 (by
  have _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := by
    intro _raw_i10 h_130 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_130)
    have h_130 : Litex.In _value_i10 (Litex.R (M := M)) := h_130
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_132 : Litex.In _value_i11 (Litex.R (M := M))) (h_96 : (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote _value_i9))), ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_148 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _value_i9 _value_i12 h_131 h_148 True.intro) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_131 _Host_i11 _rep_i11 _value_i11 h_132 h_96
          have h_147 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)), (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i9) (Litex.denote _value_i16)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i15 _rep_i15 _value_i15 _membership_i15
                    exact ((Litex.surjectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote _value_i9)).mp h_96) (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15)
                )
            )
          have h_98 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_148 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i11 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _value_i9 _value_i12 h_131 h_148 True.intro) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_161 : Litex.In _value_i11 (Litex.R (M := M)) :=
                      h_132
                    rcases (h_147 _value_i11 h_161) with ⟨_value_i12, h_148, h_97⟩
                    have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
                    have _exist_match_1 : Litex.Same _value_i11 _value_i11 := (Litex.sameRefl _value_i11)
                    have _exist_match_2 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _value_i9 _value_i12 h_131 h_148 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _value_i9 _value_i12 h_131 h_148 True.intro) := (Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _value_i9 _value_i12 h_131 h_148 True.intro))
                    exact ⟨_value_i12, h_148, h_97⟩
                  )
                )
            )
          exact h_98
        )
      )
  )

theorem h_171 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_173 : Litex.IsSet _value_i17) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_174 : Litex.IsSet _value_i18) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_176 : Litex.In _value_i19 (by
  have _checked_header : ∀ (_raw_i20 : M.Value), M.mem _raw_i20 (Litex.denote _value_i17) → ((fun (_raw_i20 : M.Value) => True) _raw_i20) → True := by
    intro _raw_i20 h_175 _
    let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_175)
    have h_175 : Litex.In _value_i20 _value_i17 := h_175
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.isSet _value_i17) (Litex.isSet _value_i18) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input)))) (h_168 : (Litex.bijectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19))), (((Litex.injectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19))) ∧ ((Litex.surjectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_173 _Host_i18 _rep_i18 _value_i18 h_174 _Host_i19 _rep_i19 _value_i19 h_176 h_168
          have h_195 : (Litex.injectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_168).1
                )
            )
          have h_196 : (Litex.surjectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_168).2
                )
            )
          have h_169 : (Litex.injectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)) :=
            (by
              litex_checked_step =>
                exact (
                  h_195
                )
            )
          have h_203 : ∀ {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_membership_i23 : M.mem (Litex.denote _value_i23) (Litex.denote _value_i17)) {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_membership_i24 : M.mem (Litex.denote _value_i24) (Litex.denote _value_i17)) (h_204 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i19) (Litex.denote _value_i23)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i19) (Litex.denote _value_i24)))), ((Litex.denote _value_i23) = (Litex.denote _value_i24)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i23 _rep_i23 _value_i23 _membership_i23 _Host_i24 _rep_i24 _value_i24 _membership_i24 h_204
                    exact h_169 (Litex.denote _value_i23) _membership_i23 (Litex.denote _value_i24) _membership_i24 h_204)
                )
            )
          have h_170 : (Litex.surjectiveValue (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)) :=
            (by
              litex_checked_step =>
                exact (
                  h_196
                )
            )
          have h_214 : ∀ {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_membership_i25 : M.mem (Litex.denote _value_i25) (Litex.denote _value_i18)), (∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i26) (Litex.denote _value_i17)), ((Litex.denote _value_i25) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i19) (Litex.denote _value_i26)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i25 _rep_i25 _value_i25 _membership_i25
                    exact ((Litex.surjectiveValue_iff (Litex.denote _value_i17) (Litex.denote _value_i18) (Litex.denote _value_i19)).mp h_170) (Litex.semanticObject (Litex.denote _value_i25) (Litex.isSet _value_i25)) _membership_i25)
                )
            )
          exact (And.intro h_169 h_170)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_mapping_x5f_property_x5f_inference_x2f_statement_x2e_lit
