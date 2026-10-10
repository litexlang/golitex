import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_successor_x5f_affine_x5f_identity_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
  exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num))))))
theorem h_93 : Litex.In (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_75 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_75)
    have h_75 : Litex.In _value_i2 (Litex.N (M := M)) := h_75
    have h_76 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (Litex.naturalNonnegative _value_i2 h_75)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_94 : Litex.Same (_object_i1 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
  exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num)))))) :=
  (Litex.sameRefl (_object_i1 (M := M)))

theorem h_96 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_109 : Litex.In _value_i3 (Litex.N (M := M))), Litex.Same (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro)))) (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109))) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_109
    have h_110 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (Litex.naturalNonnegative _value_i3 h_109)
    have h_95 : Litex.Same (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro)))) (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109))) :=
      (((congrArg₂ M.mulValue (Eq.refl (M.number (2 : ℂ))) (by
        let _litex_original := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_93 (M := M)) h_109 True.intro)
        let _litex_literal := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
          intro _raw_i2 h_14 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
          have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (Litex.naturalNonnegative _value_i2 h_14)
          change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
          exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num)))))) _value_i3 (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
          intro _raw_i2 h_14 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
          have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (Litex.naturalNonnegative _value_i2 h_14)
          change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
          exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num))))))) h_109 True.intro)
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_94 (M := M))) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from rfl))
      ))).trans (((Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109))) ((2 : ℂ) * ((Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109)) + (1 : ℂ))) ((2 : ℂ) + ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (Litex.numberInC (M := M) (1 : ℂ))) (2 : ℂ) ((Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109)) + (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteAdd _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109)) (1 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_109)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109)) (2 : ℂ) ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.naturalToComplex _value_i3 h_109) (2 : ℂ) (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_109)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_109)))) (by ring))).trans ((Eq.refl (M.addValue (M.number (2 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote _value_i3))))).symm))
    exact h_95
  )

theorem h_1023 : Litex.Same (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_93 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) True.intro) (Litex.number (M := M) (3 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_93 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
      have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (Litex.naturalNonnegative _value_i2 h_14)
      change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
      exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num)))))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
      have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (Litex.naturalNonnegative _value_i2 h_14)
      change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.N (M := M))
      exact (Litex.addInN _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num))))))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_94 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))
end LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_successor_x5f_affine_x5f_identity_x2f_statement_x2e_lit
