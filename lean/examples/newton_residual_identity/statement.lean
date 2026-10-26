import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_identity_x2f_statement_x2e_lit

universe u v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.addValue _raw_i2 (M.divValue (M.number (2 : ℂ)) _raw_i2)) (M.number (2 : ℂ)))) (by
  intro _raw_i2 h_43 h_1
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_43)
  have h_43 : Litex.In _value_i2 (Litex.R (M := M)) := h_43
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i2;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) h_1);
    (Litex.add _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_43) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i2 (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_43) (Litex.divInC _wd_1_1 _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i2;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) h_1);
    (Litex.add _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_43) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i2 (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_43) (Litex.divInC _wd_1_1 _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_43) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.addInR _value_i2 ((_atomic_wd_1_0).val.left).val.right h_43 (Litex.divInR (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_43 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))
theorem h_357 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_358 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_361 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_374 : Litex.In _value_i4 (Litex.R (M := M))) (h_359 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w10 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i4 (h_357 (M := M)) h_374 h_359);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (2 : ℂ))))
  let _object_w11 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _value_i4;
  let _wd_3_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_3_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) h_359);
  (Litex.sub _wd_3_0 _wd_3_1 (M.real_subset_complex _ h_374) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_3_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) (_atomic_wd_1_0).wd.2.2))));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.subInC _value_i4 (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_374) (Litex.divInC _wd_2_1 _value_i4 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.divInR (_atomic_wd_1_0).val.left _wd_1_1 (Litex.subInR _value_i4 ((_atomic_wd_1_0).val.left).val.right h_374 (Litex.divInR _wd_1_1 _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_374 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact (by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_374 h_359
          let _object_w10 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i4 (h_357 (M := M)) h_374 h_359);
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (2 : ℂ))))
          let _object_w11 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _value_i4;
          let _wd_3_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_3_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) h_359);
          (Litex.sub _wd_3_0 _wd_3_1 (M.real_subset_complex _ h_374) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_3_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) (_atomic_wd_1_0).wd.2.2))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInC _value_i4 (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_374) (Litex.divInC _wd_2_1 _value_i4 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.divInR (_atomic_wd_1_0).val.left _wd_1_1 (Litex.subInR _value_i4 ((_atomic_wd_1_0).val.left).val.right h_374 (Litex.divInR _wd_1_1 _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_374 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          have h_360 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.subValue (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.divValue (M.addValue (Litex.denote _value_i4) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i4))) (M.number (2 : ℂ))) from by
                    let _litex_original := ((_equal_wd_1_0).val.left).val.base
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i4;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_374 h_359))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_358 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.addValue _raw_i2 (M.divValue (M.number (2 : ℂ)) _raw_i2)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.addValue _raw_i2 (M.divValue (M.number (2 : ℂ)) _raw_i2)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i4) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i4))) (M.number (2 : ℂ))) from rfl))
                  ) (Eq.refl (M.number (2 : ℂ)))) (Eq.refl (M.number (2 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := _value_i4;
                  let _wd_4_1 := (((_equal_wd_1_1).val.base).val.left).val.right;
                  (Litex.add _wd_4_0 _wd_4_1 (M.real_subset_complex _ h_374) (by
                    let _atomic_wd_1_0 := _wd_4_1
                    exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_4_0 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) (_atomic_wd_1_0).wd.2.2))));
                  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.div _wd_3_0 _wd_3_1 (by
                    let _atomic_wd_1_0 := _wd_3_0
                    exact (Litex.addInC _value_i4 (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_374) (Litex.divInC _wd_3_1 _value_i4 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_3_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
                  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.divInR (_atomic_wd_1_0).val.left _wd_2_1 (Litex.addInR _value_i4 ((_atomic_wd_1_0).val.left).val.right h_374 (Litex.divInR _wd_2_1 _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_374 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.sub _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.divInC ((_atomic_wd_1_0).val.base).val.left _wd_1_1 (Litex.addInC _value_i4 (((_atomic_wd_1_0).val.base).val.left).val.right (M.real_subset_complex _ h_374) (Litex.divInC _wd_1_1 _value_i4 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_374) ((((_atomic_wd_1_0).val.base).val.left).val.right).wd.2.2)) (Litex.numberInC (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.base).wd.2.2)
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.numberInC (M := M) (2 : ℂ))));
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)) + ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)))) / (2 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ)) ((((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)) - ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)))) / (2 : ℂ)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := ((_equal_wd_2_0).val.left).val.base
                    exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.addInR _value_i4 ((_atomic_wd_1_0).val.left).val.right h_374 (Litex.divInR (Litex.number (M := M) (2 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_374 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (((_equal_wd_2_0).val.left).val.base).val.left (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.left).val.base).wd.1 (((_equal_wd_2_0).val.left).val.base).wd.2.1 (((_equal_wd_2_0).val.left).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 ((((_equal_wd_2_0).val.left).val.base).val.left).val.right ((((_equal_wd_2_0).val.left).val.base).val.left).wd.1 ((((_equal_wd_2_0).val.left).val.base).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_374)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i4 (((((_equal_wd_2_0).val.left).val.base).val.left).val.right).wd.1 (((((_equal_wd_2_0).val.left).val.base).val.left).val.right).wd.2.1 (((((_equal_wd_2_0).val.left).val.base).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_374)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denotePowNatReal (_equal_wd_2_1).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (_equal_wd_2_1).val.base
                    exact (Litex.divInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.subInR _value_i4 ((_atomic_wd_1_0).val.left).val.right h_374 (Litex.divInR (Litex.number (M := M) (2 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_374 (((_atomic_wd_1_0).val.left).val.right).wd.2.2)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv ((_equal_wd_2_1).val.base).val.left (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_1).val.base).wd.1 ((_equal_wd_2_1).val.base).wd.2.1 ((_equal_wd_2_1).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteSub _value_i4 (((_equal_wd_2_1).val.base).val.left).val.right (((_equal_wd_2_1).val.base).val.left).wd.1 (((_equal_wd_2_1).val.base).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_374)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i4 ((((_equal_wd_2_1).val.base).val.left).val.right).wd.1 ((((_equal_wd_2_1).val.base).val.left).val.right).wd.2.1 ((((_equal_wd_2_1).val.base).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_374)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i4 (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_374)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_374)) h_359
                    have _litex_nz_1 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))).trans ((Eq.refl (M.powValue (M.divValue (M.subValue (Litex.denote _value_i4) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i4))) (M.number (2 : ℂ))) (M.number (2 : ℂ))))).symm))))
                )
            )
          exact h_360
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_identity_x2f_statement_x2e_lit
