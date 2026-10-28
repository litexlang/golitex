import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_nested_x5f_calls_x2f_statement_x2e_lit

universe u
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

theorem h_134 : (by
  let _equal_wd_1_0 := (let _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_53 (M := M)) (by
    let _atomic_wd_1_0 := _object_w7
    exact (by
      let _litex_return_call := _object_w7
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_53 (M := M)) (by
          let _atomic_wd_1_0 := _object_w7
          exact (by
            let _litex_return_call := _object_w7
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (_equal_wd_1_0).val.argument = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from by
          let _litex_original := (let _object_w6 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w6 (h_53 (M := M)) (by
          let _atomic_wd_1_0 := _object_w6
          exact (by
            let _litex_return_call := _object_w6
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (let _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w5 (h_53 (M := M)) (by
          let _atomic_wd_1_0 := _object_w5
          exact (by
            let _litex_return_call := _object_w5
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)))))
        )).trans (((Eq.refl (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (M.number (1 : ℂ))))).trans (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (M.number (1 : ℂ))) = M.number (4 : ℂ) from ((congrArg₂ M.addValue (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (3 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))).symm)))
      )
  )

theorem h_173 : (by
  let _equal_wd_1_0 := (let _object_w7 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_53 (M := M)) (by
    let _atomic_wd_1_0 := _object_w7
    exact (by
      let _litex_return_call := _object_w7
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_134 (M := M))
      )
  )

theorem h_265 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_0).val.left = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)) (show Litex.denote (_equal_wd_1_0).val.right = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (((Eq.refl (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))))).trans (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))) = M.number (7 : ℂ) from ((congrArg₂ M.addValue (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num))))))) (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) = M.number (4 : ℂ) from ((congrArg₂ M.addValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (3 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans ((M.add_numbers (3 : ℂ) (4 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))).symm)))
      )
  )

theorem h_350 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_265 (M := M))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i4) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i4))) (by
  intro _raw_i4 h_365 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_365)
  have h_365 : Litex.In _value_i4 (Litex.R (M := M)) := h_365
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_365 True.intro);
    let _wd_1_1 := _wd_1_0;
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0)))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_365 True.intro);
    let _wd_1_1 := _wd_1_0;
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0)))))
    exact (by
      let _litex_real_result := _atomic_wd_1_0
      exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
    ))))
theorem h_802 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_803 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_824 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_802 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_802 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i3 (M := M)) = (Litex.denote (_object_i3 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_802 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i3 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_803 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_802 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i3 (M := M)) = (Litex.denote (_object_i3 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) from congrArg (fun (_raw_i4 : M.Value) => (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i4) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i4))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))))).trans (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) = M.number (6 : ℂ) from ((congrArg₂ M.addValue (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num))))))) (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans ((M.add_numbers (3 : ℂ) (3 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

theorem h_830 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_802 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_824 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_nested_x5f_calls_x2f_statement_x2e_lit
