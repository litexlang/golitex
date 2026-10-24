import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_bijection_x2f_statement_x2e_lit

universe u v3 v4 v15
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change Litex.In _value_i2 (Litex.R (M := M))
  exact h_14))
theorem h_21 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_22 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_25 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_29 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_30 : Litex.In _value_i4 (Litex.R (M := M))) (h_23 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_21 (M := M)) h_29 True.intro)
  let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_21 (M := M)) h_30 True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_29 _Host_i4 _rep_i4 _value_i4 h_30 h_23
          have h_43 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_29
                )
            )
          have h_44 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_30
                )
            )
          have h_26 : (by
            let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_21 (M := M)) h_43 True.intro)
            exact Litex.Same _value_i3 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_21 (M := M)) h_43 True.intro);
                  (show Litex.Same _value_i3 _equal_wd_1_1 from ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (Litex.denote _value_i3) from by
                    have _litex_residual : (Litex.denote _value_i3) = (Litex.denote _value_i3) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (Litex.denote _value_i3) from by
                    let _litex_original := _equal_wd_1_1
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_43 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i3) from rfl))
                  ))).trans _litex_residual)).symm))
                )
            )
          have h_27 : (by
            let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_21 (M := M)) h_44 True.intro)
            exact Litex.Same _equal_wd_1_0 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_21 (M := M)) h_44 True.intro);
                  (show Litex.Same _equal_wd_1_0 _value_i4 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.denote _value_i4) from by
                    have _litex_residual : (Litex.denote _value_i4) = (Litex.denote _value_i4) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.denote _value_i4) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i4;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_44 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i4) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_28 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_26).trans h_23)).trans h_27)
                )
            )
          exact h_28
        )
      )
  )

theorem h_150 : (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((Litex.injectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mpr (by
          intro _x _hx _y _hy _eq
          exact (show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_171 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_172 : Litex.In _value_i8 (Litex.R (M := M))) (h_167 : (by
          let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_21 (M := M)) h_171 True.intro)
          let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i8 (h_21 (M := M)) h_172 True.intro)
          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i7 _value_i8 from (by
          intro _Host_i7 _rep_i7 _value_i7 h_171 _Host_i8 _rep_i8 _value_i8 h_172 h_167
          exact ((h_25 (M := M)) _value_i7 h_171 _value_i8 h_172 h_167)
        )) _x _hx _y _hy _eq))
      )
  )

theorem h_215 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) (h_216 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i13)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i14)))), ((Litex.denote _value_i13) = (Litex.denote _value_i14)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i14 _rep_i14 _value_i14 _membership_i14 h_216
          exact (h_150 (M := M)) (Litex.denote _value_i13) _membership_i13 (Litex.denote _value_i14) _membership_i14 h_216)
      )
  )

theorem h_220 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_223 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_224 : Litex.In _value_i16 (Litex.R (M := M))), Litex.Same _value_i15 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i16 (h_21 (M := M)) h_224 True.intro) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_223
          have h_230 : Litex.In _value_i15 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_223
                )
            )
          have h_222 : ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_231 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i15 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i17 (h_21 (M := M)) h_231 True.intro) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i17 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)
                    have h_242 : Litex.In _value_i17 (Litex.R (M := M)) := h_230
                    have h_243 : Litex.Same _value_i17 _value_i15 := rfl
                    have h_244 : (by
                      let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i15 (h_21 (M := M)) (Litex.inOfSame _value_i17 _value_i15 (Litex.R (M := M)) (Litex.R (M := M)) h_243 (show @Eq M.Value _ _ from Eq.refl _) h_242) True.intro)
                      exact Litex.Same _value_i15 _equal_wd_1_1) := (let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i15 (h_21 (M := M)) (Litex.inOfSame _value_i17 _value_i15 (Litex.R (M := M)) (Litex.R (M := M)) h_243 (show @Eq M.Value _ _ from Eq.refl _) h_242) True.intro);
                    (show Litex.Same _value_i15 _equal_wd_1_1 from ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i15)) = (Litex.denote _value_i15) from by
                      have _litex_residual : (Litex.denote _value_i15) = (Litex.denote _value_i15) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i15)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i15)) = (Litex.denote _value_i15) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i15;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inOfSame _value_i17 _wd_1_1 (Litex.R (M := M)) (Litex.R (M := M)) h_243 (show @Eq M.Value _ _ from Eq.refl _) h_242) True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i15) from rfl))
                    ))).trans _litex_residual)).symm))
                    exact ⟨_value_i17, h_242, h_244⟩
                )
            )
          exact h_222
        )
      )
  )

theorem h_301 : (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((Litex.surjectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mpr (by
          intro _y _hy
          exact (show ∀ {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_322 : Litex.In _value_i20 (Litex.R (M := M))), ∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (h_323 : Litex.In _value_i21 (Litex.R (M := M))), Litex.Same _value_i20 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i21 (h_21 (M := M)) h_323 True.intro) from (by
          intro _Host_i20 _rep_i20 _value_i20 h_322
          exact ((h_220 (M := M)) _value_i20 h_322)
        )) _y _hy))
      )
  )

theorem h_361 : ∀ {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (_membership_i26 : M.mem (Litex.denote _value_i26) (M.standard Litex.StandardSetValue.real)), (∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i27) (M.standard Litex.StandardSetValue.real)), ((Litex.denote _value_i26) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i27)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i26 _rep_i26 _value_i26 _membership_i26
          exact ((Litex.surjectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mp (h_301 (M := M))) (Litex.semanticObject (Litex.denote _value_i26) (Litex.isSet _value_i26)) _membership_i26)
      )
  )

theorem h_362 : (Litex.bijectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ⟨(show (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) from (h_150 (M := M))), (show (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) from (h_301 (M := M)))⟩
      )
  )

theorem h_422 : (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_362 (M := M))).1
      )
  )

theorem h_423 : (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_362 (M := M))).2
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_bijection_x2f_statement_x2e_lit
