import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by
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
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14))
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14))
    exact (Litex.mulInN (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) h_14))))
theorem h_61 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_62 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_76 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_76)
  have h_76 : Litex.In _value_i4 (Litex.N (M := M)) := h_76
  have h_77 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i4 h_76)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_76) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_76) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_76
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
    ))))
theorem h_138 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_139 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

noncomputable def _object_w9 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_61 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) True.intro)

theorem h_140 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w9 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.number (6 : ℂ)) from by
    have _litex_residual : (M.mulValue (M.number (2 : ℂ)) (M.number (3 : ℂ))) = (M.number (6 : ℂ)) := (let _equal_wd_2_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) ((2 : ℂ) * (3 : ℂ)) (6 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_62 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (2 : ℂ)) (M.number (3 : ℂ))) from rfl))
  ))).trans _litex_residual)))

noncomputable def _object_w11 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_138 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) True.intro)

theorem h_188 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w11 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ))) = (M.number (9 : ℂ)) from by
    have _litex_residual : (M.powValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) = (M.number (9 : ℂ)) := (let _equal_wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) ((3 : ℂ) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_139 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))

def prop_5 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) : Prop :=
  ∃ (h_237 : Litex.In _value_i5 (Litex.N (M := M))), (by
    let _object_w14 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_138 (M := M)) h_237 True.intro)
    exact Litex.In _object_w14 (Litex.N (M := M))
  )

theorem h_248 : ((prop_5 (M := M)) (Litex.number (M := M) (3 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)) (by
    let _atomic_wd_2_0 := (_object_w11 (M := M))
    exact (by
      let _litex_return_call := (_object_w11 (M := M))
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.N (M := M)) (Litex.N (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.N (M := M))) (Litex.callInOutput _litex_return_call))))

theorem h_274 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
  (by rcases (h_248 (M := M)) with ⟨h_237, h_236⟩; exact h_237)

theorem h_275 : Litex.In (_object_w11 (M := M)) (Litex.N (M := M)) :=
  (by rcases (h_248 (M := M)) with ⟨h_237, h_236⟩; exact h_236)
end LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit
