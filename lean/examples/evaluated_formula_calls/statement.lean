import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_formula_x5f_calls_x2f_statement_x2e_lit

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

theorem h_61 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from ((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (((((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_54 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
        )).trans (((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans ((show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).symm))))
      )
  )

theorem h_65 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_61 (M := M))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_135 h_136 h_67
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_135)
  have h_135 : Litex.In _value_i4 (Litex.R (M := M)) := h_135
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_136)
  have h_136 : Litex.In _value_i5 (Litex.R (M := M)) := h_136
  have h_67 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i5 = (M.number (0 : ℂ))))
            exact h_67)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_136) h_67)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_135) (M.real_subset_complex _ h_136) h_67)
    exact (Litex.divInR _value_i4 _value_i5 h_135 h_136 (_atomic_wd_1_0).wd.2.2))))
theorem h_236 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_237 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_260 : (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_236 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_236 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from ((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (3 : ℂ))])))).trans (((((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (3 : ℂ))])) = (M.divValue (M.number (6 : ℂ)) (M.number (3 : ℂ))) from by
          let _litex_original := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_236 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          let _litex_formula := (_object_i3 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_237 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _ _).mpr _litex_original.wd.2)
          exact _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) = (M.divValue (M.number (6 : ℂ)) (M.number (3 : ℂ))) from congrArg (fun (_pair : M.Value × M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 _raw_i5)) _pair.1 _pair.2) (Litex.FiniteFunction.unpack_pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))))
        )).trans (((Eq.refl (M.divValue (M.number (6 : ℂ)) (M.number (3 : ℂ))))).trans (show (M.divValue (M.number (6 : ℂ)) (M.number (3 : ℂ))) = M.number (2 : ℂ) from ((congrArg₂ M.divValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (6 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))))).trans ((show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).symm))))
      )
  )

theorem h_272 : (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_236 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_260 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_formula_x5f_calls_x2f_statement_x2e_lit
