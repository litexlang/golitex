import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_direction_x5f_magnitude_x5f_functions_x2f_statement_x2e_lit

universe u v5 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.sign _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sign _value_i2 h_14)
    exact (Litex.signInZ _atomic_wd_1_0))))
theorem h_32 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_33 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (Litex.absValue (M := M) _raw_i4)) (by
  intro _raw_i4 h_47 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_47)
  have h_47 : Litex.In _value_i4 (Litex.R (M := M)) := h_47
  change (by
    let _atomic_wd_1_0 := (Litex.abs _value_i4 h_47)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.abs _value_i4 h_47)
    exact (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    ))))
theorem h_69 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_70 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_72 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_77 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i5 (h_32 (M := M)) h_77 True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_69 (M := M)) h_77 True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 _value_i5) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_77
          have h_250 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_77
                )
            )
          let _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i5 (h_32 (M := M)) h_250 True.intro)

          let _object_w12 := (Litex.sign _value_i5 h_250)

          have h_73 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = ((Litex.signValue (M := M)) (Litex.denote _value_i5)) from by
                    have _litex_residual : ((Litex.signValue (M := M)) (Litex.denote _value_i5)) = ((Litex.signValue (M := M)) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = ((Litex.signValue (M := M)) (Litex.denote _value_i5)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i5;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_250 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w13 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_69 (M := M)) h_250 True.intro)

          let _object_w14 := (Litex.abs _value_i5 h_250)

          have h_74 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)) = (Litex.absValue (M := M) (Litex.denote _value_i5)) from by
                    have _litex_residual : (Litex.absValue (M := M) (Litex.denote _value_i5)) = (Litex.absValue (M := M) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)) = (Litex.absValue (M := M) (Litex.denote _value_i5)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                    let _wd_1_1 := _value_i5;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_250 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_70 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (Litex.absValue (M := M) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (Litex.absValue (M := M) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w15 := (let _wd_1_0 := _object_w11;
          let _wd_1_1 := _object_w13;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.integerToComplex _object_w11 (Litex.callInOutput _object_w11))) (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.realToComplex _object_w13 (Litex.callInOutput _object_w13)))))

          let _object_w16 := (let _wd_1_0 := _object_w12;
          let _wd_1_1 := _object_w14;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w14
            exact (M.real_subset_complex _ (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            )))))

          have h_75 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = ((Litex.signValue (M := M)) (Litex.denote _value_i5)) from h_73) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)) = (Litex.absValue (M := M) (Litex.denote _value_i5)) from h_74))
                )
            )
          have h_76 : (by
            let _equal_wd_1_0 := _object_w16
            exact Litex.Same _equal_wd_1_0 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.signTimesAbs (_object_w16).val.left true)
                )
            )
          exact ((h_75).trans h_76)
        )
      )
  )

theorem h_716 : (by
  have h_717 : (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_32 (M := M)) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact h_717) True.intro));
    let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.argument;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _wd_2_0 (h_69 (M := M)) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact h_717) True.intro));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
    let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_717 : (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))))
                )
            )
          have h_718 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_32 (M := M)) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact h_717) True.intro));
          let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _wd_2_0 (h_69 (M := M)) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact h_717) True.intro));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_72 (M := M)) (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) h_717)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_32 (M := M)) (by
          let _atomic_wd_1_0 := _wd_2_0
          exact h_717) True.intro));
        let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.argument;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _wd_2_0 (h_69 (M := M)) (by
          let _atomic_wd_1_0 := _wd_2_0
          exact h_717) True.intro));
        (Litex.mul _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
        let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_718).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )

theorem h_1058 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1083 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_1084 : Litex.In _value_i8 (Litex.R (M := M))), (by
  let _object_w39 := (let _object_w28 := (Litex.mul _value_i7 _value_i8 (M.real_subset_complex _ h_1083) (M.real_subset_complex _ h_1084));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w28 (h_32 (M := M)) (by
    let _atomic_wd_1_0 := _object_w28
    exact (Litex.mulInR _value_i7 _value_i8 h_1083 h_1084)) True.intro))
  let _object_w40 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) h_1083 True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i8 (h_32 (M := M)) h_1084 True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact (by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_1083 _Host_i8 _rep_i8 _value_i8 h_1084
          let _object_w39 := (let _object_w28 := (Litex.mul _value_i7 _value_i8 (M.real_subset_complex _ h_1083) (M.real_subset_complex _ h_1084));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w28 (h_32 (M := M)) (by
            let _atomic_wd_1_0 := _object_w28
            exact (Litex.mulInR _value_i7 _value_i8 h_1083 h_1084)) True.intro))
          let _object_w40 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) h_1083 True.intro);
          let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i8 (h_32 (M := M)) h_1084 True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
          have h_1057 : (by
            let _equal_wd_1_0 := _object_w39
            let _equal_wd_1_1 := _object_w40
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w39;
                  let _equal_wd_1_1 := _object_w40;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8))) = ((Litex.signValue (M := M)) (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w38 := (_equal_wd_1_0).val.argument;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w38 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w38
                      exact (Litex.mulInR _value_i7 _value_i8 h_1083 h_1084)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (M.mulValue (Litex.denote _value_i7) (Litex.denote _value_i8))) from rfl))
                  )).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
                  (Litex.sign _wd_1_0 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.mulInR _value_i7 _value_i8 h_1083 h_1084))));
                  let _equal_wd_2_1 := (let _wd_1_0 := (Litex.sign _value_i7 h_1083);
                  let _wd_1_1 := (Litex.sign _value_i8 h_1084);
                  (Litex.mul _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.signProduct (_equal_wd_2_1).val.left (_equal_wd_2_1).val.right false)))).trans ((congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) from by
                    let _litex_original := (_equal_wd_1_1).val.left
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1083 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) from rfl))
                  ) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = ((Litex.signValue (M := M)) (Litex.denote _value_i8)) from by
                    let _litex_original := (_equal_wd_1_1).val.right
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i8;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1084 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.denote _value_i8)) from rfl))
                  ))).symm))))
                )
            )
          exact h_1057
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_direction_x5f_magnitude_x5f_functions_x2f_statement_x2e_lit
