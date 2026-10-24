import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_function_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.N (M := M))) (Litex.denote (Litex.NPos (M := M))) (Litex.isSet (Litex.N (M := M))) (Litex.isSet (Litex.NPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.factorialValue (M := M) _raw_i2)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.N (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.factorialValue (M := M) _raw_i2)) _raw_i2) (Litex.denote (Litex.NPos (M := M))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
    have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i2 h_14)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.factorial _value_i2 h_14)
      exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.factorial _value_i2 h_14)
      exact (Litex.factorialInNPos _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.N (M := M))) (Litex.denote (Litex.NPos (M := M))) (Litex.isSet (Litex.N (M := M))) (Litex.isSet (Litex.NPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_33 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_34 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w7 := (let _litex_call_arg_0 := (Litex.number (M := M) (5 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_33 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)), True.intro⟩))

theorem h_35 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (5 : ℂ))) = (M.number (120 : ℂ)) from by
          have _litex_residual : ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) = (M.number (120 : ℂ)) := (let _equal_wd_2_0 := (Litex.factorial (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (120 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (120 : ℂ)) (120 : ℂ) (120 : ℂ) (let _factorial := _equal_wd_2_0;
          let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
          (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (5 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (5 : ℂ))) = ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
        (let _litex_call_arg_0 := _wd_1_1;
        Litex.callOnDomain (Litex.N (M := M)) (Litex.NPos (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_34 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.factorialValue (M := M) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))); exact rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_function_x2f_statement_x2e_lit
