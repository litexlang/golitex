import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_composition_x5f_identities_x2f_statement_x2e_lit

universe u
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
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_93 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => _raw_i5) (by
  intro _raw_i5 h_136 h_94
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_136)
  have h_136 : Litex.In _value_i5 (Litex.R (M := M)) := h_136
  have h_94 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i5 = (M.number (0 : ℂ))))
            exact h_94)
        )
    )
  change Litex.In _value_i5 (Litex.R (M := M))
  exact h_136))
theorem h_143 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_144 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_w20 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) _raw_i7))) (by
  intro _raw_i7 h_188 h_146
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_188)
  have h_188 : Litex.In _value_i7 (Litex.R (M := M)) := h_188
  have h_146 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_146)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i4 (M := M)) _value_i7 (h_143 (M := M)) h_188 h_146);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w19 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_146
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
        have _litex_residual : (Litex.denote _value_i7) = (Litex.denote _value_i7) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
        let _litex_original := _object_w19
        let _litex_literal := (let _wd_2_0 := (_object_i4 (M := M));
        let _wd_2_1 := _value_i7;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_188 h_146))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_144 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => _raw_i5) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => _raw_i5) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i7) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i4 (M := M)) _value_i7 (h_143 (M := M)) h_188 h_146);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w19 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_146
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
        have _litex_residual : (Litex.denote _value_i7) = (Litex.denote _value_i7) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
        let _litex_original := _object_w19
        let _litex_literal := (let _wd_2_0 := (_object_i4 (M := M));
        let _wd_2_1 := _value_i7;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_188 h_146))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_144 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => _raw_i5) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => _raw_i5) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i7) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i4 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i4 (M := M)) (_object_i4 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))))) ((h_144 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i4 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i7) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) _raw_i7) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
  intro _raw_i7 h_188 h_146
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_188)
  have h_188 : Litex.In _value_i7 (Litex.R (M := M)) := h_188
  have h_146 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_146)
        )
    )
  let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (_object_i4 (M := M)) _value_i7 (h_143 (M := M)) h_188 h_146);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w18 (h_92 (M := M)) (by
  let _atomic_wd_1_0 := _object_w18
  exact (by
    let _litex_return_call := _object_w18
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
  let _atomic_wd_1_0 := _object_w18
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := h_146
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _value_i7) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
    have _litex_residual : (Litex.denote _value_i7) = (Litex.denote _value_i7) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
    let _litex_original := _object_w18
    let _litex_literal := (let _wd_2_0 := (_object_i4 (M := M));
    let _wd_2_1 := _value_i7;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_188 h_146))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_144 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) => _raw_i5) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => _raw_i5) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i7) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  ))))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members _preimage_guard_0))

theorem h_145 : (by
  let _equal_wd_1_0 := (_object_w20 (M := M))
  exact Litex.Same _equal_wd_1_0 (_object_i1 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w20 (M := M));
        (show Litex.Same _equal_wd_1_0 (_object_i1 (M := M)) from (Litex.composeRightIdentity _equal_wd_1_0 (_object_i4 (M := M)) (h_144 (M := M)) (by intro x; rfl) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by rfl))))
      )
  )

noncomputable def _object_w51 := (let _wd_1_0 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9))) (by
  intro _raw_i9 h_618 h_576
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
  have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
  have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_576)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w25
      exact (by
        let _litex_return_call := _object_w25
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w25
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
        let _litex_original := _object_w25
        let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
        let _wd_3_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_618 h_576))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w25
      exact (by
        let _litex_return_call := _object_w25
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w25
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
        let _litex_original := _object_w25
        let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
        let _wd_3_1 := _value_i9;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_618 h_576))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
  intro _raw_i9 h_618 h_576
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
  have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
  have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_576)
        )
    )
  let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w24 (h_92 (M := M)) (by
  let _atomic_wd_1_0 := _object_w24
  exact (by
    let _litex_return_call := _object_w24
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
  let _atomic_wd_1_0 := _object_w24
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
    exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
    let _litex_original := _object_w24
    let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
    let _wd_3_1 := _value_i9;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_618 h_576))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  ))))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members _preimage_guard_0));
(by
  have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))))) := (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i11))) (by
  intro _raw_i11 h_1694 h_1652
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1694)
  have h_1694 : Litex.In _value_i11 (Litex.R (M := M)) := h_1694
  have h_1652 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i11 = (M.number (0 : ℂ))))
            exact h_1652)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i11 (h_92 (M := M)) h_1694 h_1652);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w30 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w30
      exact (by
        let _litex_return_call := _object_w30
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w30
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i11 h_1694) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_1652) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
        let _litex_original := _object_w30
        let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
        let _wd_3_1 := _value_i11;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_1694 h_1652))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i11 (h_92 (M := M)) h_1694 h_1652);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w30 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w30
      exact (by
        let _litex_return_call := _object_w30
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w30
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i11 h_1694) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_1652) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
        let _litex_original := _object_w30
        let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
        let _wd_3_1 := _value_i11;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_1694 h_1652))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
  intro _raw_i11 h_1694 h_1652
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1694)
  have h_1694 : Litex.In _value_i11 (Litex.R (M := M)) := h_1694
  have h_1652 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i11 = (M.number (0 : ℂ))))
            exact h_1652)
        )
    )
  let _composition_call := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i11 (h_92 (M := M)) h_1694 h_1652);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w29 (h_92 (M := M)) (by
  let _atomic_wd_1_0 := _object_w29
  exact (by
    let _litex_return_call := _object_w29
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
  let _atomic_wd_1_0 := _object_w29
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)
    exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i11 h_1694) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_1652) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i11 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1694) h_1652)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from by
    let _litex_original := _object_w29
    let _litex_literal := (let _wd_3_0 := (_object_i1 (M := M));
    let _wd_3_1 := _value_i11;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_3_0 _wd_3_1 (Litex.formulaFnInFnSet _wd_3_0) h_1694 h_1652))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i11)) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  ))))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members _preimage_guard_0)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ)))))) _range_signature_0))

noncomputable def _object_w52 := (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_91 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_91)
    have h_91 : Litex.In _value_i2 (Litex.R (M := M)) := h_91
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_92 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) _range_signature_0)

theorem h_575 : (by
  let _atomic_wd_1_0 := (_object_w51 (M := M))
  let _atomic_wd_1_1 := (_object_w52 (M := M))
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w51 (M := M))
          let _atomic_wd_1_1 := (_object_w52 (M := M))
          exact (by
            have _composition_interface := (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9))) (by
            intro _raw_i9 h_618 h_576
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
            have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
            have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                      exact h_576)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  let _litex_return_call := _object_w25
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  let _litex_original := _object_w25
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i9;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  let _litex_return_call := _object_w25
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  let _litex_original := _object_w25
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i9;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
            intro _raw_i9 h_618 h_576
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
            have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
            have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                      exact h_576)
                  )
              )
            let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w24 (h_92 (M := M)) (by
            let _atomic_wd_2_0 := _object_w24
            exact (by
              let _litex_return_call := _object_w24
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
            let _atomic_wd_2_0 := _object_w24
            exact (by
              change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
              have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
              let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
              exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
              exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
              have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
              let _litex_original := _object_w24
              let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
              let _wd_2_1 := _value_i9;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
            ))).trans _litex_residual)).symm)) _unfold_child
            ))))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members _preimage_guard_0)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            exact Litex.composeRangeSubset (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9))) (by
            intro _raw_i9 h_618 h_576
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
            have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
            have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                      exact h_576)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  let _litex_return_call := _object_w25
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  let _litex_original := _object_w25
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i9;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  let _litex_return_call := _object_w25
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w25
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
                  let _litex_original := _object_w25
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i9;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i9) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
            intro _raw_i9 h_618 h_576
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_618)
            have h_618 : Litex.In _value_i9 (Litex.R (M := M)) := h_618
            have h_576 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                      exact h_576)
                  )
              )
            let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i9 (h_92 (M := M)) h_618 h_576);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w24 (h_92 (M := M)) (by
            let _atomic_wd_2_0 := _object_w24
            exact (by
              let _litex_return_call := _object_w24
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
            let _atomic_wd_2_0 := _object_w24
            exact (by
              change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
              have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
              let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)
              exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i9 h_618) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_576) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
              exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_618) h_576)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
              have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from by
              let _litex_original := _object_w24
              let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
              let _wd_2_1 := _value_i9;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_618 h_576))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)) from rfl))
            ))).trans _litex_residual)).symm)) _unfold_child
            ))))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members _preimage_guard_0)) _atomic_wd_1_0 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by rfl)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_composition_x5f_identities_x2f_statement_x2e_lit
