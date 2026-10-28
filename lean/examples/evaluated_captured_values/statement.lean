import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_captured_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.number (M := M) (10 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (10 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (10 : ℂ)))
      )
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue (Litex.denote (_object_i1 (M := M))) _raw_i3)) (by
  intro _raw_i3 h_18 _
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18)
  have h_18 : Litex.In _value_i3 (Litex.R (M := M)) := h_18
  change (by
    let _atomic_wd_1_0 := (Litex.add (_object_i1 (M := M)) _value_i3 (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ h_18))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add (_object_i1 (M := M)) _value_i3 (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ h_18))
    exact (Litex.addInR (_object_i1 (M := M)) _value_i3 (h_3 (M := M)) h_18))))
theorem h_91 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i2 (M := M)))
      )
  )
theorem h_92 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i2 (M := M)))
      )
  )

theorem h_103 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (2 : ℂ))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (2 : ℂ))) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i2 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_92 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (2 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) from congrArg (fun (_raw_i3 : M.Value) => (M.addValue (Litex.denote (_object_i1 (M := M))) _raw_i3)) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))))
        )).trans (((congrArg₂ M.addValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.refl (M.number (2 : ℂ))))).trans (show (M.addValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (12 : ℂ) from ((congrArg₂ M.addValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.add_numbers (10 : ℂ) (2 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = (12 : ℂ)))).symm)))
      )
  )

theorem h_109 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_103 (M := M))
      )
  )

theorem h_253 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (27 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
        let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro);
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (27 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (27 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_0).val.left = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)) (show Litex.denote (_equal_wd_1_0).val.right = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl))) (((Eq.refl (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ)))))).trans (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ)))) = M.number (27 : ℂ) from ((congrArg₂ M.addValue (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i2 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_92 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg (fun (_raw_i3 : M.Value) => (M.addValue (Litex.denote (_object_i1 (M := M))) _raw_i3)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))
        )).trans (((congrArg₂ M.addValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.refl (M.number (3 : ℂ))))).trans (show (M.addValue (M.number (10 : ℂ)) (M.number (3 : ℂ))) = M.number (13 : ℂ) from ((congrArg₂ M.addValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.add_numbers (10 : ℂ) (3 : ℂ)).trans (congrArg M.number (by norm_num))))))) (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ))) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (4 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i2 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_92 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (4 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (4 : ℂ))) from congrArg (fun (_raw_i3 : M.Value) => (M.addValue (Litex.denote (_object_i1 (M := M))) _raw_i3)) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl))))
        )).trans (((congrArg₂ M.addValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.refl (M.number (4 : ℂ))))).trans (show (M.addValue (M.number (10 : ℂ)) (M.number (4 : ℂ))) = M.number (14 : ℂ) from ((congrArg₂ M.addValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num)))).trans ((M.add_numbers (10 : ℂ) (4 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans ((M.add_numbers (13 : ℂ) (14 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (27 : ℂ))).trans (congrArg M.number (by norm_num : (27 : ℂ) = (27 : ℂ)))).symm)))
      )
  )

theorem h_386 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (27 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_253 (M := M))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.addValue _raw_i5 (M.number (1 : ℂ)))) (by
  intro _raw_i5 h_401 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_401)
  have h_401 : Litex.In _value_i5 (Litex.R (M := M)) := h_401
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_401) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_401) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i5 (Litex.number (M := M) (1 : ℂ)) h_401 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_470 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_471 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_482 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (_object_i1 (M := M)) (h_470 (M := M)) (h_3 (M := M)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (_object_i1 (M := M)) (h_470 (M := M)) (h_3 (M := M)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote (_object_i1 (M := M)))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i4 (M := M)) = (Litex.denote (_object_i4 (M := M))) from rfl) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote (_object_i1 (M := M)))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote (_object_i1 (M := M)))) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (_object_i1 (M := M)) (h_470 (M := M)) (h_3 (M := M)) True.intro)
          let _litex_formula := (_object_i4 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_471 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (_object_i1 (M := M)) (h_470 (M := M)) (h_3 (M := M)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote (_object_i1 (M := M)))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i4 (M := M)) = (Litex.denote (_object_i4 (M := M))) from rfl) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) from congrArg (fun (_raw_i5 : M.Value) => (M.addValue _raw_i5 (M.number (1 : ℂ)))) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl))))
        )).trans (((congrArg₂ M.addValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.refl (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (10 : ℂ)) (M.number (1 : ℂ))) = M.number (11 : ℂ) from ((congrArg₂ M.addValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (10 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (11 : ℂ))).trans (congrArg M.number (by norm_num : (11 : ℂ) = (11 : ℂ)))).symm)))
      )
  )

theorem h_488 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (_object_i1 (M := M)) (h_470 (M := M)) (h_3 (M := M)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_482 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_captured_x5f_values_x2f_statement_x2e_lit
