import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_rotation_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number Complex.I) _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.C (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) Complex.I) _value_i2 (Litex.numberInC (M := M) Complex.I) h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) Complex.I) _value_i2 (Litex.numberInC (M := M) Complex.I) h_14)
    exact (Litex.mulInC (Litex.number (M := M) Complex.I) _value_i2 (Litex.numberInC (M := M) Complex.I) h_14))))
theorem h_43 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_44 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_46 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_51 : Litex.In _value_i3 (Litex.C (M := M))), (by
  let _equal_wd_1_0 := (let _object_w6 := (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_43 (M := M)) h_51 True.intro);
  (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w6 (h_43 (M := M)) (by
    let _atomic_wd_1_0 := _object_w6
    exact (by
      let _litex_return_call := _object_w6
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  let _equal_wd_1_1 := (Litex.neg _value_i3 h_51)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_51
          have h_121 : Litex.In _value_i3 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_51
                )
            )
          let _object_w17 := (let _object_w8 := (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_43 (M := M)) h_121 True.intro);
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w8 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _object_w8
            exact (by
              let _litex_return_call := _object_w8
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))

          let _object_w18 := (let _wd_1_0 := (Litex.number (M := M) Complex.I);
          let _wd_1_1 := (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_43 (M := M)) h_121 True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) Complex.I) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call)))))

          have h_47 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) from by
                    have _litex_residual : (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w16 := (_equal_wd_1_1).val.right;
                    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w16 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w16
                      exact (by
                        let _litex_return_call := _object_w16
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number Complex.I) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue (M.number Complex.I) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w19 := (_object_w17).val.argument

          let _object_w20 := (Litex.mul (Litex.number (M := M) Complex.I) _value_i3 (Litex.numberInC (M := M) Complex.I) h_121)

          have h_48 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  let _equal_wd_1_1 := _object_w20;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.denote _value_i3)) from by
                    have _litex_residual : (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.denote _value_i3)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)))).trans (by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_121 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number Complex.I) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue (M.number Complex.I) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.denote _value_i3)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w21 := (let _wd_1_0 := (Litex.number (M := M) Complex.I);
          let _wd_1_1 := _object_w20;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) Complex.I) (by
            let _atomic_wd_1_0 := _object_w20
            exact (Litex.mulInC _wd_1_0 _value_i3 (Litex.numberInC (M := M) Complex.I) h_121))))

          have h_49 : (by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.mulValue (show (Litex.denote (Litex.number (M := M) Complex.I)) = (Litex.denote (Litex.number (M := M) Complex.I)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.mulValue (Litex.denote (Litex.number (M := M) Complex.I)) (Litex.denote _value_i3)) from h_48))
                )
            )
          let _object_w22 := (Litex.neg _value_i3 h_121)

          have h_50 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w21;
                  let _equal_wd_1_1 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (Complex.I * (Complex.I * (Litex.NativeBridge.asComplex _value_i3 h_121))) (- (Litex.NativeBridge.asComplex _value_i3 h_121)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) Complex.I) (_object_w21).val.right (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.denoteMul (Litex.number (M := M) Complex.I) _value_i3 (_object_w20).wd.1 (_object_w20).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.asComplex_spec _value_i3 h_121))) (Litex.NativeBridge.denoteNeg _value_i3 (_equal_wd_1_1).wd _ (Litex.NativeBridge.asComplex_spec _value_i3 h_121)) (by litex_normalize_complex))))
                )
            )
          exact ((((h_47).trans h_49)).trans h_50)
        )
      )
  )

theorem h_1467 : (by
  have h_1468 : (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I))
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I))
            exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _object_w27 := (let _wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_43 (M := M)) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact h_1468) True.intro));
    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w27 (h_43 (M := M)) (by
      let _atomic_wd_1_0 := _object_w27
      exact (by
        let _litex_return_call := _object_w27
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
    (Litex.neg _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact h_1468)))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1468 : (by
            let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I))
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I))
                    exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))
                )
            )
          have h_1469 : Litex.Same (let _object_w27 := (let _wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact h_1468) True.intro));
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w27 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _object_w27
            exact (by
              let _litex_return_call := _object_w27
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro)) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_1468))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_46 (M := M)) (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I)) h_1468)
                )
            )
          exact (let _equal_wd_1_0 := (let _object_w27 := (let _wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_43 (M := M)) (by
          let _atomic_wd_1_0 := _wd_2_0
          exact h_1468) True.intro));
        (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w27 (h_43 (M := M)) (by
          let _atomic_wd_1_0 := _object_w27
          exact (by
            let _litex_return_call := _object_w27
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro));
        let _equal_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.neg _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact h_1468)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1469).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_rotation_x2f_statement_x2e_lit
