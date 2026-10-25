import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reordered_x5f_function_x5f_domains_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  rintro _raw_i2 h_71 ⟨h_1, h_2⟩
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_71)
  have h_71 : Litex.In _value_i2 (Litex.R (M := M)) := h_71
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (1 : ℂ))))
            exact h_2)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_71) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_71) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_71 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_114 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_115 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by
  rintro _raw_i6 h_186 ⟨h_116, h_117⟩
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_186)
  have h_186 : Litex.In _value_i6 (Litex.R (M := M)) := h_186
  have h_116 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i6 = (M.number (1 : ℂ))))
            exact h_116)
        )
    )
  have h_117 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i6 = (M.number (0 : ℂ))))
            exact h_117)
        )
    )
  change Litex.In _value_i6 (Litex.R (M := M))
  exact h_186))
theorem h_197 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_198 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w40 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (((¬ (_raw_i9 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) _raw_i9))) (by
  rintro _raw_i9 h_270 ⟨h_200, h_201⟩
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_270)
  have h_270 : Litex.In _value_i9 (Litex.R (M := M)) := h_270
  have h_200 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (1 : ℂ))))
            exact h_200)
        )
    )
  have h_201 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_201)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (_object_i5 (M := M)) _value_i9 (h_197 (M := M)) h_270 (And.intro h_200 h_201));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _object_w33 (h_114 (M := M)) (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        let _litex_return_call := _object_w33
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (And.intro (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_201
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        let _litex_original := _object_w33
        let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
        let _wd_2_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      )) (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (1 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ))) := h_200
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (1 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        let _litex_original := _object_w33
        let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
        let _wd_2_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      )))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (_object_i5 (M := M)) _value_i9 (h_197 (M := M)) h_270 (And.intro h_200 h_201));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _object_w33 (h_114 (M := M)) (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        let _litex_return_call := _object_w33
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (And.intro (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_201
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        let _litex_original := _object_w33
        let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
        let _wd_2_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      )) (by
      let _atomic_wd_2_0 := _object_w33
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (1 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ))) := h_200
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (1 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
        let _litex_original := _object_w33
        let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
        let _wd_2_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      )))))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ)))))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((h_115 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))) ((h_198 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (((¬ (_raw_i9 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain := (by
  rintro _raw_i9 h_270 ⟨h_200, h_201⟩
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_270)
  have h_270 : Litex.In _value_i9 (Litex.R (M := M)) := h_270
  have h_200 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (1 : ℂ))))
            exact h_200)
        )
    )
  have h_201 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_201)
        )
    )
  let _composition_call := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (_object_i5 (M := M)) _value_i9 (h_197 (M := M)) h_270 (And.intro h_200 h_201));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _object_w32 (h_114 (M := M)) (by
  let _atomic_wd_1_0 := _object_w32
  exact (by
    let _litex_return_call := _object_w32
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (And.intro (by
  let _atomic_wd_1_0 := _object_w32
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_201
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
    have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
    let _litex_original := _object_w32
    let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
    let _wd_2_1 := _value_i9;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  )) (by
  let _atomic_wd_1_0 := _object_w32
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (1 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ))) := h_200
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i9) (Litex.denote (Litex.number (M := M) (1 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (1 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
    have _litex_residual : (Litex.denote _value_i9) = (Litex.denote _value_i9) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9) from by
    let _litex_original := _object_w32
    let _litex_literal := (let _wd_2_0 := (_object_i5 (M := M));
    let _wd_2_1 := _value_i9;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_270 (And.intro h_200 h_201)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_198 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_raw_i6 : M.Value) => _raw_i6) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i9) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  )))))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((h_115 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _litex_input) _).mp _preimage_domain
  rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members (And.intro _preimage_guard_0 _preimage_guard_1)))

theorem h_199 : (by
  let _equal_wd_1_0 := (_object_w40 (M := M))
  exact Litex.Same _equal_wd_1_0 (_object_i1 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w40 (M := M));
        (show Litex.Same _equal_wd_1_0 (_object_i1 (M := M)) from (by
          have h_844 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_847 : Litex.In _value_i12 (Litex.R (M := M))) (h_839 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))) (h_840 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))), ((Litex.In _value_i12 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))) ∧ (¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)))))) := (by
            intro _Host_i12 _rep_i12 _value_i12 h_847 h_839 h_840
            have h_841 : Litex.In _value_i12 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_847
                  )
              )
            have h_842 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_840
                  )
              )
            have h_843 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_839
                  )
              )
            exact (And.intro h_841 (And.intro h_842 h_843))
          )
          have h_871 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_874 : Litex.In _value_i13 (Litex.R (M := M))) (h_866 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (1 : ℂ))) (h_867 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i13 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i13 (Litex.number (M := M) (1 : ℂ)))))) := (by
            intro _Host_i13 _rep_i13 _value_i13 h_874 h_866 h_867
            have h_868 : Litex.In _value_i13 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_874
                  )
              )
            have h_869 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_867
                  )
              )
            have h_870 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_866
                  )
              )
            exact (And.intro h_868 (And.intro h_869 h_870))
          )
          exact (Litex.composeRightIdentity _equal_wd_1_0 (_object_i5 (M := M)) (h_198 (M := M)) (by intro x; rfl) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((h_115 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _litex_input) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_844 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
        ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (((¬ (_raw_i6 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i6 = (M.number (0 : ℂ))))))) _litex_input) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_871 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
        ) x hx⟩)))
        )))
      )
  )

noncomputable def _object_i14 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) (fun (_raw_i15 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i15)) (by
  rintro _raw_i15 h_963 ⟨h_893, h_894⟩
  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_963)
  have h_963 : Litex.In _value_i15 (Litex.R (M := M)) := h_963
  have h_893 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i15 = (M.number (1 : ℂ))))
            exact h_893)
        )
    )
  have h_894 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i15 = (M.number (0 : ℂ))))
            exact h_894)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_963))
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_963))
    exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_963)))))
theorem h_1040 : Litex.In (_object_i14 (M := M)) (Litex.fnSet ((_object_i14 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i14 (M := M)))
      )
  )
theorem h_1041 : Litex.Same (_object_i14 (M := M)) (_object_i14 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i14 (M := M)))
      )
  )

theorem h_1043 : Litex.Same (_object_i1 (M := M)) (_object_i14 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1049 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_1062 : Litex.In _value_i18 (Litex.R (M := M))) (h_1044 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ))) (h_1045 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ))), ((Litex.In _value_i18 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ))) ∧ (¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)))))) := (by
            intro _Host_i18 _rep_i18 _value_i18 h_1062 h_1044 h_1045
            have h_1046 : Litex.In _value_i18 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1062
                  )
              )
            have h_1047 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1045
                  )
              )
            have h_1048 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1044
                  )
              )
            exact (And.intro h_1046 (And.intro h_1047 h_1048))
          )
          have h_1086 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_1099 : Litex.In _value_i19 (Litex.R (M := M))) (h_1081 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ))) (h_1082 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i19 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)))))) := (by
            intro _Host_i19 _rep_i19 _value_i19 h_1099 h_1081 h_1082
            have h_1083 : Litex.In _value_i19 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1099
                  )
              )
            have h_1084 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1082
                  )
              )
            have h_1085 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1081
                  )
              )
            exact (And.intro h_1083 (And.intro h_1084 h_1085))
          )
          have _pointwise : ∀ {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_1134 : Litex.In _value_i20 (Litex.R (M := M))) (h_1118 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))) (h_1119 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (1 : ℂ))), (by
            let _object_w62 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _value_i20 (h_114 (M := M)) h_1134 (And.intro h_1118 h_1119))
            let _object_w63 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) (_object_i14 (M := M)) _value_i20 (h_1040 (M := M)) h_1134 (And.intro h_1119 h_1118))
            exact (by
              let _equal_wd_1_0 := _object_w62
              let _equal_wd_1_1 := _object_w63
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i20 _rep_i20 _value_i20 h_1134 h_1118 h_1119
            let _object_w62 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _value_i20 (h_114 (M := M)) h_1134 (And.intro h_1118 h_1119))
            let _object_w63 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) (_object_i14 (M := M)) _value_i20 (h_1040 (M := M)) h_1134 (And.intro h_1119 h_1118))
            have h_1121 : (by
              let _equal_wd_1_0 := _object_w62
              let _equal_wd_1_1 := _object_w63
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w62;
                    let _equal_wd_1_1 := _object_w63;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i20)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i14 (M := M))) (Litex.denote _value_i20)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i20) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i20)) := (let _equal_wd_2_0 := (Litex.add _value_i20 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1134) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _equal_wd_2_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1134));
                      (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_1134)) + (1 : ℂ)) ((1 : ℂ) + (Litex.NativeBridge.asComplex _value_i20 (Litex.realToComplex _value_i20 h_1134))) (Litex.NativeBridge.denoteAdd _value_i20 (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i20 (Litex.realToComplex _value_i20 h_1134)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) _value_i20 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i20 (Litex.realToComplex _value_i20 h_1134))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i20)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i20)) = (M.addValue (Litex.denote _value_i20) (M.number (1 : ℂ))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i20;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1134 (And.intro h_1118 h_1119)))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_115 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i20) (M.number (1 : ℂ))) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i14 (M := M))) (Litex.denote _value_i20)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i14 (M := M))) (Litex.denote _value_i20)) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i20)) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i14 (M := M));
                      let _wd_1_1 := _value_i20;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1134 (And.intro h_1119 h_1118)))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1041 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) (fun (_raw_i15 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i15)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i15 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i15)) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i20)) from rfl))
                    ))).symm))))
                  )
              )
            exact h_1121
          )
          apply Litex.functionExtOnDomain (_object_i1 (M := M)) (_object_i14 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ)))))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((h_115 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i14 (M := M)) (_object_i14 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))) ((h_1041 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i14 (M := M)))) (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _litex_input) _).mp _preimage_domain
            rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
            have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            have _domain_target := h_1049 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
            have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
          ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.C (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => (((¬ (_raw_i15 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i15 = (M.number (0 : ℂ))))))) _litex_input) _).mp _preimage_domain
            rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
            have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            have _domain_target := h_1086 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
            have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
          ) x hx⟩))
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _litex_input) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _repack : _preimage_input = _preimage_input := rfl
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i14 (M := M))) x) _repack) (_pointwise (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reordered_x5f_function_x5f_domains_x2f_statement_x2e_lit
