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
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14)) (Litex.N (M := M))
  exact (Litex.mulInN (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) h_14)))
theorem h_91 : Litex.In (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_74 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_74)
    have h_74 : Litex.In _value_i2 (Litex.N (M := M)) := h_74
    have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (Litex.naturalNonnegative _value_i2 h_74)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_92 : Litex.Same (_object_i1 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14)) (Litex.N (M := M))
  exact (Litex.mulInN (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) h_14))) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_106 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_106)
  have h_106 : Litex.In _value_i4 (Litex.N (M := M)) := h_106
  have h_107 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (Litex.naturalNonnegative _value_i4 h_106)
  change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
  exact (Litex.powStructuralInN (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_106 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))))))
theorem h_210 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := by
    intro _raw_i4 h_187 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_187)
    have h_187 : Litex.In _value_i4 (Litex.N (M := M)) := h_187
    have h_188 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (Litex.naturalNonnegative _value_i4 h_187)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_211 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_106 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_106)
  have h_106 : Litex.In _value_i4 (Litex.N (M := M)) := h_106
  have h_107 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (Litex.naturalNonnegative _value_i4 h_106)
  change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
  exact (Litex.powStructuralInN (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_106 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num)))))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_212 : Litex.Same (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro) (Litex.number (M := M) (6 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_91 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
      have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (Litex.naturalNonnegative _value_i2 h_14)
      change Litex.In (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14)) (Litex.N (M := M))
      exact (Litex.mulInN (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) h_14))) (Litex.number (M := M) (3 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
      have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (Litex.naturalNonnegative _value_i2 h_14)
      change Litex.In (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i2 h_14)) (Litex.N (M := M))
      exact (Litex.mulInN (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) h_14)))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_92 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue (M.number (2 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (2 : ℂ)) (M.number (3 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (6 : ℂ)) ((2 : ℂ) * (3 : ℂ)) (6 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num)))

theorem h_260 : Litex.Same (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro) (Litex.number (M := M) (9 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
      intro _raw_i4 h_106 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_106)
      have h_106 : Litex.In _value_i4 (Litex.N (M := M)) := h_106
      have h_107 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
        (Litex.naturalNonnegative _value_i4 h_106)
      change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
      exact (Litex.powStructuralInN (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_106 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num)))))) (Litex.number (M := M) (3 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
      intro _raw_i4 h_106 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_106)
      have h_106 : Litex.In _value_i4 (Litex.N (M := M)) := h_106
      have h_107 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
        (Litex.naturalNonnegative _value_i4 h_106)
      change Litex.In (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
      exact (Litex.powStructuralInN (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i4 h_106) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_106 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_211 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.powNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.number (M := M) (9 : ℂ)) ((3 : ℂ) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num)))

def prop_5 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) : Prop :=
  ∃ (h_309 : Litex.In _value_i5 (Litex.N (M := M))), Litex.In (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_210 (M := M)) h_309 True.intro) (Litex.N (M := M))

theorem h_382 : ((prop_5 (M := M)) (Litex.number (M := M) (3 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) (Litex.inOfSame (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro) (Litex.N (M := M)) (Litex.N (M := M)) (Litex.sameRefl (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro)) (Litex.sameRefl (Litex.N (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro))))

theorem h_408 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) :=
  (by rcases (h_382 (M := M)) with ⟨h_309, h_308⟩; exact h_309)

theorem h_411 : Litex.In (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_210 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInNOfEq (3 : ℂ) (3 : ℕ) (by norm_num))) True.intro) (Litex.N (M := M)) :=
  (by rcases (h_382 (M := M)) with ⟨h_309, h_308⟩; exact h_308)
end LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit
