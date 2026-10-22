import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_function_x5f_affine_x5f_arithmetic_x2f_statement_x2e_lit

universe u v3 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (3 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (3 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

theorem h_56 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_57 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_57 True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_57));
  let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_57))
    exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_57))) (Litex.numberInC (M := M) (6 : ℂ))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_57
    have h_189 : Litex.In _value_i3 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_57
          )
      )
    exact (((congrArg₂ M.mulValue (Eq.refl (M.number (2 : ℂ))) (by
      let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_189 True.intro)
      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
      let _wd_1_1 := _value_i3;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_189 True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (3 : ℂ))) from rfl))
    ))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.add _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_189) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_189) (Litex.numberInC (M := M) (3 : ℂ)))
      exact (Litex.addInC _value_i3 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_189) (Litex.numberInC (M := M) (3 : ℂ))))));
    let _equal_wd_2_1 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_189));
    let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_189))
      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_189))) (Litex.numberInC (M := M) (6 : ℂ))));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((2 : ℂ) * ((Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_189)) + (3 : ℂ))) (((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i3 (Litex.realToComplex _value_i3 h_189))) + (6 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i3 (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_189)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_1).val.left (Litex.number (M := M) (6 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i3 ((_equal_wd_2_1).val.left).wd.1 ((_equal_wd_2_1).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.realToComplex _value_i3 h_189))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (by ring!))))).trans ((Eq.refl (M.addValue (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i3)) (M.number (6 : ℂ))))).symm))
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.subValue _raw_i6 (M.number (1 : ℂ)))) (by
  intro _raw_i6 h_1305 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1305)
  have h_1305 : Litex.In _value_i6 (Litex.R (M := M)) := h_1305
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1305) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1305) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.subInR _value_i6 (Litex.number (M := M) (1 : ℂ)) h_1305 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_1359 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i5 (M := M)))
theorem h_1360 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (Litex.sameRefl (_object_i5 (M := M)))

theorem h_1362 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1363 : Litex.In _value_i7 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_1363 True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_1363 True.intro);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i7 (h_1359 (M := M)) h_1363 True.intro);
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
  let _wd_1_1 := (Litex.number (M := M) (8 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_2_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i7 (h_1359 (M := M)) h_1363 True.intro);
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0)))))
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (Litex.numberInC (M := M) (8 : ℂ))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i7 _rep_i7 _value_i7 h_1363
    have h_1816 : Litex.In _value_i7 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_1363
          )
      )
    exact (((congrArg₂ M.addValue (by
      let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_1816 True.intro)
      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
      let _wd_1_1 := _value_i7;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1816 True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i7) (M.number (3 : ℂ))) from rfl))
    ) (by
      let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_1816 True.intro)
      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
      let _wd_1_1 := _value_i7;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1816 True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (3 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i7) (M.number (3 : ℂ))) from rfl))
    ))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ)));
    let _wd_1_1 := (Litex.add _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ)))
      exact (Litex.addInC _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ)))
      exact (Litex.addInC _value_i7 (Litex.number (M := M) (3 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (3 : ℂ))))));
    let _equal_wd_2_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_2_1 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ))))));
    let _wd_1_1 := (Litex.number (M := M) (8 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (2 : ℂ));
      let _wd_2_1 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
        let _atomic_wd_2_0 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ)))
        exact (Litex.subInC _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ))))))
      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (2 : ℂ)) (Litex.subInC _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1816) (Litex.numberInC (M := M) (1 : ℂ))))) (Litex.numberInC (M := M) (8 : ℂ))));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1816)) + (3 : ℂ)) + ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1816)) + (3 : ℂ))) (((2 : ℂ) * ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 h_1816)) - (1 : ℂ))) + (8 : ℂ)) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i7 (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_1816)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteAdd _value_i7 (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_1816)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_1).val.left (Litex.number (M := M) (8 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_1).val.left).val.right ((_equal_wd_2_1).val.left).wd.1 ((_equal_wd_2_1).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteSub _value_i7 (Litex.number (M := M) (1 : ℂ)) (((_equal_wd_2_1).val.left).val.right).wd.1 (((_equal_wd_2_1).val.left).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 h_1816)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))) (by ring!))))).trans ((congrArg₂ M.addValue (congrArg₂ M.mulValue (Eq.refl (M.number (2 : ℂ))) (by
      let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i7 (h_1359 (M := M)) h_1816 True.intro)
      let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
      let _wd_1_1 := _value_i7;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1816 True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1360 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.subValue _raw_i6 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (M.subValue _raw_i6 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (Litex.denote _value_i7) (M.number (1 : ℂ))) from rfl))
    )) (Eq.refl (M.number (8 : ℂ))))).symm))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_function_x5f_affine_x5f_arithmetic_x2f_statement_x2e_lit
