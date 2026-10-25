import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_function_x5f_application_x2f_statement_x2e_lit

universe u v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 _raw_i2)) _captured_input)) (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i2))) (by
      intro _raw_i3 h_117 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_117)
      have h_117 : Litex.In _value_i3 (Litex.R (M := M)) := h_117
      change (by
        let _atomic_wd_2_0 := (Litex.add _value_i3 _value_i2 (M.real_subset_complex _ h_117) (M.real_subset_complex _ h_14))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (Litex.add _value_i3 _value_i2 (M.real_subset_complex _ h_117) (M.real_subset_complex _ h_14))
        exact (Litex.addInR _value_i3 _value_i2 h_117 h_14))));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i2))) (by
      intro _raw_i3 h_117 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_117)
      have h_117 : Litex.In _value_i3 (Litex.R (M := M)) := h_117
      change (by
        let _atomic_wd_2_0 := (Litex.add _value_i3 _value_i2 (M.real_subset_complex _ h_117) (M.real_subset_complex _ h_14))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (Litex.add _value_i3 _value_i2 (M.real_subset_complex _ h_117) (M.real_subset_complex _ h_14))
        exact (Litex.addInR _value_i3 _value_i2 h_117 h_14))));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
    exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _atomic_wd_1_0)))))
theorem h_225 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_226 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_228 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_241 : Litex.In _value_i4 (Litex.R (M := M))), (by
  let _object_w6 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_225 (M := M)) h_241 True.intro)
  let _object_w7 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241))
  exact (by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_241
          let _object_w6 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_225 (M := M)) h_241 True.intro)
          let _object_w7 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_241))
          have h_227 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from by
                    have _litex_residual : (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) _captured_input)) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i4;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_241 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_226 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 _raw_i2)) _captured_input)) (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 _raw_i2)) _captured_input)) (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) _captured_input)) (M.number (1 : ℂ))) from rfl))
                  ))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) _captured_input)) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from by
                    let _litex_original := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) (by
                      intro _raw_i3 h_325 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_325)
                      have h_325 : Litex.In _value_i3 (Litex.R (M := M)) := h_325
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_325) (M.real_subset_complex _ h_241))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_325) (M.real_subset_complex _ h_241))
                        exact (Litex.addInR _value_i3 _value_i4 h_325 h_241))));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) (by
                      intro _raw_i3 h_430 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_430)
                      have h_430 : Litex.In _value_i3 (Litex.R (M := M)) := h_430
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_430) (M.real_subset_complex _ h_241))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i3 _value_i4 (M.real_subset_complex _ h_430) (M.real_subset_complex _ h_241))
                        exact (Litex.addInR _value_i3 _value_i4 h_430 h_241))));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (Litex.denote _value_i4))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_227
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_function_x5f_application_x2f_statement_x2e_lit
