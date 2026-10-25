import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_function_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.powerSet (Litex.R (M := M))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun _difference_element : M.Value => ¬ M.mem _difference_element (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M)))))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun _difference_element : M.Value => ¬ M.mem _difference_element (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M)))))) _raw_i2) (Litex.denote (Litex.powerSet (Litex.R (M := M)))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
      let _wd_1_1 := (let _setElement_0 := _value_i2;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0);
      (Litex.setMinus _wd_1_0 _wd_1_1))
      let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
      let _wd_1_1 := (let _setElement_0 := _value_i2;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0);
      (Litex.setMinus _wd_1_0 _wd_1_1))
      let _atomic_wd_1_1 := (Litex.powerSet (Litex.R (M := M)))
      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 (Litex.R (M := M))).mpr (by
        let _atomic_wd_2_0 := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := _value_i2;
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1))
        exact (let _set := _atomic_wd_2_0; Litex.setMinusSubsetLeft _set.val.left _set.val.right)))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (Litex.powerSet (Litex.R (M := M)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (Litex.powerSet (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_23 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_24 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w5 := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_23 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩))

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.R (M := M));
let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.setMinus _wd_1_0 _wd_1_1))

theorem h_25 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (Litex.denote _equal_wd_1_1) from by
          have _litex_residual : (Litex.denote _equal_wd_1_1) = (Litex.denote _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (Litex.denote _equal_wd_1_1) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (let _litex_call_arg_0 := _wd_1_1;
        Litex.callOnDomain (Litex.R (M := M)) (Litex.powerSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_24 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun _difference_element : M.Value => ¬ M.mem _difference_element (Litex.SetSemantics.insertValue _raw_i2 (Litex.SetSemantics.emptyValue (M := M)))))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _equal_wd_1_1); exact rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_53 : (by
  let _atomic_wd_1_1 := (_object_w5 (M := M))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w5 (M := M))
          exact (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w6 (M := M)) _atomic_wd_1_1 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((((Litex.sameRefl _atomic_wd_1_1)).trans (h_25 (M := M)))).symm (by
            let _atomic_wd_2_1 := (_object_w6 (M := M))
            exact (let _set := _atomic_wd_2_1; (Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), (by
              let _atomic_wd_3_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (by
                let _set := _atomic_wd_3_1
                exact (Litex.notInInsert (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Litex.notInEmpty (Litex.number (M := M) (1 : ℂ))))))⟩))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_function_x2f_statement_x2e_lit
