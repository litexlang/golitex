import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_real_x5f_reciprocal_x2f_statement_x2e_lit

universe u v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by
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
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_43) h_1)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_43) h_1)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_43 (_atomic_wd_1_0).wd.2.2))))
theorem h_92 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_93 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_92 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

noncomputable def _object_w9 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_94 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  let _equal_wd_1_1 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (let _equal_wd_1_0 := (_object_w8 (M := M));
  let _equal_wd_1_1 := (_object_w9 (M := M));
  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))

theorem h_248 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_261 : Litex.In _value_i4 (Litex.R (M := M))) (h_246 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w12 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i4 (h_92 (M := M)) h_261 h_246)
  let _object_w13 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_261) h_246)
  exact (by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_261 h_246
    let _object_w12 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i4 (h_92 (M := M)) h_261 h_246)
    let _object_w13 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_261) h_246)
    have h_247 : (by
      let _equal_wd_1_0 := _object_w12
      let _equal_wd_1_1 := _object_w13
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w12;
            let _equal_wd_1_1 := _object_w13;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from by
              have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _wd_1_1 := _value_i4;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_261 h_246))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) from rfl))
            ))).trans _litex_residual)))
          )
      )
    exact h_247
  )
end LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_real_x5f_reciprocal_x2f_statement_x2e_lit
