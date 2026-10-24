import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_shift_x5f_bijection_x2f_statement_x2e_lit

universe u v3 v4 v15 v34
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_57 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_62 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_63 : Litex.In _value_i4 (Litex.R (M := M))) (h_55 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_62 True.intro)
  let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_63 True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_62 _Host_i4 _rep_i4 _value_i4 h_63 h_55
          have h_76 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_62
                )
            )
          have h_77 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_63
                )
            )
          let _object_w11 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_76) (Litex.numberInC (M := M) (1 : ℂ)))

          have h_58 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_76 True.intro)
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_76 True.intro);
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_1
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_76 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from rfl))
                  ))).trans _litex_residual)).symm))
                )
            )
          let _object_w12 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_77) (Litex.numberInC (M := M) (1 : ℂ)))

          have h_59 : (by
            let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_77 True.intro)
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_77 True.intro);
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) from by
                    have _litex_residual : (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i4;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_77 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_60 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_58).trans h_55)).trans h_59)
                )
            )

          have h_622 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.addCancelRightRight _value_i3 _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_76) (M.real_subset_complex _ h_77) (Litex.numberInC (M := M) (1 : ℂ)) h_60)
                )
            )
          have h_61 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_622
                )
            )
          exact h_622
        )
      )
  )

theorem h_639 : (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((Litex.injectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mpr (by
          intro _x _hx _y _hy _eq
          exact (show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_660 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_661 : Litex.In _value_i8 (Litex.R (M := M))) (h_656 : (by
          let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_660 True.intro)
          let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i8 (h_53 (M := M)) h_661 True.intro)
          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), Litex.Same _value_i7 _value_i8 from (by
          intro _Host_i7 _rep_i7 _value_i7 h_660 _Host_i8 _rep_i8 _value_i8 h_661 h_656
          exact ((h_57 (M := M)) _value_i7 h_660 _value_i8 h_661 h_656)
        )) _x _hx _y _hy _eq))
      )
  )

theorem h_704 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) (h_705 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i13)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i14)))), ((Litex.denote _value_i13) = (Litex.denote _value_i14)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i14 _rep_i14 _value_i14 _membership_i14 h_705
          exact (h_639 (M := M)) (Litex.denote _value_i13) _membership_i13 (Litex.denote _value_i14) _membership_i14 h_705)
      )
  )

theorem h_709 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_713 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_714 : Litex.In _value_i16 (Litex.R (M := M))), Litex.Same _value_i15 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i16 (h_53 (M := M)) h_714 True.intro) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_713
          have h_720 : Litex.In _value_i15 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_713
                )
            )
          let _object_w29 := (let _object_w24 := (Litex.sub _value_i15 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_720) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w24 (h_53 (M := M)) (by
            let _atomic_wd_1_0 := _object_w24
            exact (Litex.subInR _value_i15 (Litex.number (M := M) (1 : ℂ)) h_720 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) True.intro))

          have h_710 : (by
            let _equal_wd_1_0 := _object_w29
            exact Litex.Same _equal_wd_1_0 _value_i15) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w29;
                  (show Litex.Same _equal_wd_1_0 _value_i15 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ)))) = (Litex.denote _value_i15) from by
                    have _litex_residual : (M.addValue (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ))) (M.number (1 : ℂ))) = (Litex.denote _value_i15) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInC _value_i15 _wd_1_1 (M.real_subset_complex _ h_720) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))));
                    (show Litex.Same _equal_wd_2_0 _value_i15 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_720)) - (1 : ℂ)) + (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i15 (Litex.realToComplex _value_i15 h_720)) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteSub _value_i15 (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_720)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.realToComplex _value_i15 h_720)) (by ring!))))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ)))) = (M.addValue (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ))) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w28 := (_equal_wd_1_0).val.argument;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w28 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w28
                      exact (Litex.subInR _value_i15 (Litex.number (M := M) (1 : ℂ)) h_720 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.subValue (Litex.denote _value_i15) (M.number (1 : ℂ))) (M.number (1 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_712 : ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_964 : Litex.In _value_i17 (Litex.R (M := M))), Litex.Same _value_i15 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i17 (h_53 (M := M)) h_964 True.intro) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i17 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (_object_w29).val.argument) (Litex.isSet (_object_w29).val.argument)
                    have h_1022 : Litex.In _value_i17 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := (_object_w29).val.argument
                      exact (Litex.subInR _value_i15 (Litex.number (M := M) (1 : ℂ)) h_720 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
                    have h_1023 : Litex.Same _value_i17 (_object_w29).val.argument := rfl
                    have h_1024 : (by
                      let _equal_wd_1_1 := _object_w29
                      exact Litex.Same _value_i15 _equal_wd_1_1) := (h_710).symm
                    exact ⟨_value_i17, h_1022, h_1024⟩
                )
            )
          exact h_712
        )
      )
  )

theorem h_1039 : (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((Litex.surjectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mpr (by
          intro _y _hy
          exact (show ∀ {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_1060 : Litex.In _value_i20 (Litex.R (M := M))), ∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (h_1061 : Litex.In _value_i21 (Litex.R (M := M))), Litex.Same _value_i20 (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i21 (h_53 (M := M)) h_1061 True.intro) from (by
          intro _Host_i20 _rep_i20 _value_i20 h_1060
          exact ((h_709 (M := M)) _value_i20 h_1060)
        )) _y _hy))
      )
  )

theorem h_1099 : ∀ {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (_membership_i26 : M.mem (Litex.denote _value_i26) (M.standard Litex.StandardSetValue.real)), (∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i27) (M.standard Litex.StandardSetValue.real)), ((Litex.denote _value_i26) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i27)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i26 _rep_i26 _value_i26 _membership_i26
          exact ((Litex.surjectiveValue_iff (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))).mp (h_1039 (M := M))) (Litex.semanticObject (Litex.denote _value_i26) (Litex.isSet _value_i26)) _membership_i26)
      )
  )

theorem h_1100 : (Litex.bijectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ⟨(show (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) from (h_639 (M := M))), (show (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) from (h_1039 (M := M)))⟩
      )
  )

theorem h_1160 : (Litex.injectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_1100 (M := M))).1
      )
  )

theorem h_1161 : (Litex.surjectiveValue (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.denote (_object_i1 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_1100 (M := M))).2
      )
  )

theorem h_1164 : ∀ {_Host_i34 : Type v34} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_1181 : Litex.In _value_i34 (Litex.R (M := M))), (∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_1182 : Litex.In _value_i35 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i35 (h_53 (M := M)) h_1182 True.intro) _value_i34) ∧ (∀ (_unique_left_i35 : Litex.Obj (M := M) M.Value) (_member_left_i35 : M.mem (Litex.denote _unique_left_i35) (M.standard Litex.StandardSetValue.real)) (_unique_right_i35 : Litex.Obj (M := M) M.Value) (_member_right_i35 : M.mem (Litex.denote _unique_right_i35) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_left_i35)) = (Litex.denote _value_i34))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_right_i35)) = (Litex.denote _value_i34))), (Litex.denote _unique_left_i35) = (Litex.denote _unique_right_i35)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i34 _rep_i34 _value_i34 h_1181
          have h_1163 : (∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_1182 : Litex.In _value_i35 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i35 (h_53 (M := M)) h_1182 True.intro) _value_i34) ∧ (∀ (_unique_left_i35 : Litex.Obj (M := M) M.Value) (_member_left_i35 : M.mem (Litex.denote _unique_left_i35) (M.standard Litex.StandardSetValue.real)) (_unique_right_i35 : Litex.Obj (M := M) M.Value) (_member_right_i35 : M.mem (Litex.denote _unique_right_i35) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_left_i35)) = (Litex.denote _value_i34))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_right_i35)) = (Litex.denote _value_i34))), (Litex.denote _unique_left_i35) = (Litex.denote _unique_right_i35)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.bijectiveValue_preimage (M.standard Litex.StandardSetValue.real) (M.standard Litex.StandardSetValue.real) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i34) (h_1100 (M := M)) h_1181)
                )
            )
          have h_1199 : ∀ {_Host_i36 : Type _} [_rep_i36 : Litex.Representation M _Host_i36] (_value_i36 : Litex.Obj (M := M) _Host_i36) (_membership_i36 : M.mem (Litex.denote _value_i36) (M.standard Litex.StandardSetValue.real)) {_Host_i37 : Type _} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (_membership_i37 : M.mem (Litex.denote _value_i37) (M.standard Litex.StandardSetValue.real)) (h_1196 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i36)) = (Litex.denote _value_i34))) (h_1197 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i37)) = (Litex.denote _value_i34))), ((Litex.denote _value_i36) = (Litex.denote _value_i37)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i36 _rep_i36 _value_i36 _membership_i36 _Host_i37 _rep_i37 _value_i37 _membership_i37 h_1196 h_1197
                    have _unique : ∀ (_unique_left_i35 : Litex.Obj (M := M) M.Value) (_member_left_i35 : M.mem (Litex.denote _unique_left_i35) (M.standard Litex.StandardSetValue.real)) (_unique_right_i35 : Litex.Obj (M := M) M.Value) (_member_right_i35 : M.mem (Litex.denote _unique_right_i35) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_left_i35)) = (Litex.denote _value_i34))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _unique_right_i35)) = (Litex.denote _value_i34))), (Litex.denote _unique_left_i35) = (Litex.denote _unique_right_i35) := (h_1163).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i36) (Litex.isSet _value_i36)) _membership_i36 (Litex.semanticObject (Litex.denote _value_i37) (Litex.isSet _value_i37)) _membership_i37 h_1196 h_1197
                    exact _same)
                )
            )
          exact h_1163
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_shift_x5f_bijection_x2f_statement_x2e_lit
