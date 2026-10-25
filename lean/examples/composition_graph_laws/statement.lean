import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_composition_x5f_graph_x5f_laws_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_14 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_14 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_14
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ))))
theorem h_43 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_44 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
  intro _raw_i4 h_58 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_58)
  have h_58 : Litex.In _value_i4 (Litex.R (M := M)) := h_58
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_58 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_112 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_113 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.subValue _raw_i7 _raw_i6)) (by
  intro _raw_i6 _raw_i7 h_174 h_175 h_114
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_174)
  have h_174 : Litex.In _value_i6 (Litex.R (M := M)) := h_174
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_175)
  have h_175 : Litex.In _value_i7 (Litex.R (M := M)) := h_175
  have h_114 : Litex.Lt _value_i6 _value_i7 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_114)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i6 (M.real_subset_complex _ h_175) (M.real_subset_complex _ h_174))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i6 (M.real_subset_complex _ h_175) (M.real_subset_complex _ h_174))
    exact (Litex.subInR _value_i7 _value_i6 h_175 h_174))))
theorem h_335 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_336 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w52 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i3 (M := M)))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i12))) (by
  intro _raw_i12 h_933 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_933)
  have h_933 : Litex.In _value_i12 (Litex.R (M := M)) := h_933
  change (by
    let _atomic_wd_1_0 := (let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i12 (h_112 (M := M)) h_933 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14))) (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      change (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w24 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w24
      exact (by
        let _litex_return_call := _object_w24
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) _object_w26 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14))) (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      change (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w24 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w24
      exact (by
        let _litex_return_call := _object_w24
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (by
      let _atomic_wd_2_0 := _object_w26
      exact (by
        let _litex_return_call := _object_w26
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i12 (h_112 (M := M)) h_933 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14))) (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      change (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w24 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w24
      exact (by
        let _litex_return_call := _object_w24
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) _object_w26 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14))) (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      change (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w25 (h_43 (M := M)) (by
          let _atomic_wd_3_0 := _object_w25
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i14) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
      intro _raw_i14 h_1387 _
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1387)
      have h_1387 : Litex.In _value_i14 (Litex.R (M := M)) := h_1387
      let _composition_call := (let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i14 (h_112 (M := M)) h_1387 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w24 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w24
      exact (by
        let _litex_return_call := _object_w24
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (by
      let _atomic_wd_2_0 := _object_w26
      exact (by
        let _litex_return_call := _object_w26
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => True))).output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (_atomic_wd_1_0).val.argument) (Litex.composeInFnSet (_atomic_wd_1_0).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => True) (Litex.denote (_atomic_wd_1_0).val.argument)).mpr ⟨(by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.argument
      exact (by
        let _litex_return_call := (_atomic_wd_1_0).val.argument
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))), True.intro⟩)))));
Litex.compose (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i10))) (by
  intro _raw_i10 h_351 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_351)
  have h_351 : Litex.In _value_i10 (Litex.R (M := M)) := h_351
  change (by
    let _atomic_wd_1_0 := (let _object_w16 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i10 (h_112 (M := M)) h_351 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w16 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w16
      exact (by
        let _litex_return_call := _object_w16
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w16 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i10 (h_112 (M := M)) h_351 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w16 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w16
      exact (by
        let _litex_return_call := _object_w16
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i10) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i10 h_351 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_351)
  have h_351 : Litex.In _value_i10 (Litex.R (M := M)) := h_351
  let _composition_call := (let _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i10 (h_112 (M := M)) h_351 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w15 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w15
  exact (by
    let _litex_return_call := _object_w15
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i11))) (by
  intro _raw_i11 h_642 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_642)
  have h_642 : Litex.In _value_i11 (Litex.R (M := M)) := h_642
  change (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i11 h_642 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_642)
  have h_642 : Litex.In _value_i11 (Litex.R (M := M)) := h_642
  let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w18 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w18
  exact (by
    let _litex_return_call := _object_w18
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i12) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))).domain := (by
  intro _raw_i12 h_933 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_933)
  have h_933 : Litex.In _value_i12 (Litex.R (M := M)) := h_933
  let _composition_call := (let _object_w23 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i12 (h_112 (M := M)) h_933 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i13 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i13 : M.Value) => True) (fun (_raw_i13 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i13))) (by
  intro _raw_i13 h_947 _
  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_947)
  have h_947 : Litex.In _value_i13 (Litex.R (M := M)) := h_947
  change (by
    let _atomic_wd_1_0 := (let _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w22
      exact (by
        let _litex_return_call := _object_w22
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w22
      exact (by
        let _litex_return_call := _object_w22
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i13) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i13 h_947 _
  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_947)
  have h_947 : Litex.In _value_i13 (Litex.R (M := M)) := h_947
  let _composition_call := (let _object_w21 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w21 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w21
  exact (by
    let _litex_return_call := _object_w21
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) _object_w23 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i13 : M.Value) => True) (fun (_raw_i13 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i13))) (by
  intro _raw_i13 h_947 _
  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_947)
  have h_947 : Litex.In _value_i13 (Litex.R (M := M)) := h_947
  change (by
    let _atomic_wd_1_0 := (let _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w22
      exact (by
        let _litex_return_call := _object_w22
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w22
      exact (by
        let _litex_return_call := _object_w22
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i13) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i13 h_947 _
  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_947)
  have h_947 : Litex.In _value_i13 (Litex.R (M := M)) := h_947
  let _composition_call := (let _object_w21 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i13 (h_112 (M := M)) h_947 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w21 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w21
  exact (by
    let _litex_return_call := _object_w21
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (by
  let _atomic_wd_1_0 := _object_w23
  exact (by
    let _litex_return_call := _object_w23
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True)) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (fun (_raw_i11 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i11))) (by
  intro _raw_i11 h_642 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_642)
  have h_642 : Litex.In _value_i11 (Litex.R (M := M)) := h_642
  change (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w19
      exact (by
        let _litex_return_call := _object_w19
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i11) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i11 h_642 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_642)
  have h_642 : Litex.In _value_i11 (Litex.R (M := M)) := h_642
  let _composition_call := (let _object_w18 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i11 (h_112 (M := M)) h_642 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w18 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w18
  exact (by
    let _litex_return_call := _object_w18
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro))

noncomputable def _object_w53 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i19 : M.Value) => True) (fun (_raw_i19 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i3 (M := M)))) _raw_i19))) (by
  intro _raw_i19 h_2493 _
  let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_2493)
  have h_2493 : Litex.In _value_i19 (Litex.R (M := M)) := h_2493
  change (by
    let _atomic_wd_1_0 := (let _object_w39 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (fun (_raw_i23 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23))) (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      change (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      let _composition_call := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w37 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w37
      exact (by
        let _litex_return_call := _object_w37
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) _value_i19 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (fun (_raw_i23 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23))) (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      change (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      let _composition_call := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w37 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w37
      exact (by
        let _litex_return_call := _object_w37
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) h_2493 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w39
      exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True))).output (Litex.denote (_object_w39).val.function) (Litex.denote _value_i19) (Litex.composeInFnSet (_object_w39).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True) (Litex.denote _value_i19)).mpr ⟨h_2493, True.intro⟩))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w39 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (fun (_raw_i23 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23))) (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      change (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      let _composition_call := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w37 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w37
      exact (by
        let _litex_return_call := _object_w37
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) _value_i19 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) => True) (fun (_raw_i23 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23))) (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      change (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_2_0 := (let _object_w38 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w38 (h_112 (M := M)) (by
          let _atomic_wd_3_0 := _object_w38
          exact (by
            let _litex_return_call := _object_w38
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
    Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
      have _composition_checked : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i23) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
      intro _raw_i23 h_2944 _
      let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_2944)
      have h_2944 : Litex.In _value_i23 (Litex.R (M := M)) := h_2944
      let _composition_call := (let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i23 (h_112 (M := M)) h_2944 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w37 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w37
      exact (by
        let _litex_return_call := _object_w37
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
      intro _composition_input _preimage_domain
      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
      have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
      exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) h_2493 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w39
      exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True))).output (Litex.denote (_object_w39).val.function) (Litex.denote _value_i19) (Litex.composeInFnSet (_object_w39).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i24 : M.Value) => True) (Litex.denote _value_i19)).mpr ⟨h_2493, True.intro⟩))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i17 : M.Value) => True) (fun (_raw_i17 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i17))) (by
  intro _raw_i17 h_1911 _
  let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_1911)
  have h_1911 : Litex.In _value_i17 (Litex.R (M := M)) := h_1911
  change (by
    let _atomic_wd_1_0 := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i17 (h_112 (M := M)) h_1911 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w29 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w29
      exact (by
        let _litex_return_call := _object_w29
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i17 (h_112 (M := M)) h_1911 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w29 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w29
      exact (by
        let _litex_return_call := _object_w29
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i17) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
  intro _raw_i17 h_1911 _
  let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_1911)
  have h_1911 : Litex.In _value_i17 (Litex.R (M := M)) := h_1911
  let _composition_call := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i17 (h_112 (M := M)) h_1911 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w28 (h_112 (M := M)) (by
  let _atomic_wd_1_0 := _object_w28
  exact (by
    let _litex_return_call := _object_w28
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) => True) (fun (_raw_i18 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i18))) (by
  intro _raw_i18 h_2202 _
  let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2202)
  have h_2202 : Litex.In _value_i18 (Litex.R (M := M)) := h_2202
  change (by
    let _atomic_wd_1_0 := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i18 (h_112 (M := M)) h_2202 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w32 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w32
      exact (by
        let _litex_return_call := _object_w32
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w32 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i18 (h_112 (M := M)) h_2202 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w32 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w32
      exact (by
        let _litex_return_call := _object_w32
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i18) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
  intro _raw_i18 h_2202 _
  let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_2202)
  have h_2202 : Litex.In _value_i18 (Litex.R (M := M)) := h_2202
  let _composition_call := (let _object_w31 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i18 (h_112 (M := M)) h_2202 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w31 (h_112 (M := M)) (by
  let _atomic_wd_1_0 := _object_w31
  exact (by
    let _litex_return_call := _object_w31
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (by
  have _composition_checked : ∀ (_raw_i19 : M.Value), M.mem _raw_i19 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i19 : M.Value) => True) _raw_i19) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.compositionValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i3 (M := M)))) _raw_i19) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i19 h_2493 _
  let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_2493)
  have h_2493 : Litex.In _value_i19 (Litex.R (M := M)) := h_2493
  let _composition_call := (let _object_w36 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i20 : M.Value) => True) (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i20 : M.Value) => True) (fun (_raw_i20 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i20))) (by
  intro _raw_i20 h_2507 _
  let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_2507)
  have h_2507 : Litex.In _value_i20 (Litex.R (M := M)) := h_2507
  change (by
    let _atomic_wd_1_0 := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w35 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w35
      exact (by
        let _litex_return_call := _object_w35
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w35 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w35
      exact (by
        let _litex_return_call := _object_w35
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i20 : M.Value), M.mem _raw_i20 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i20 : M.Value) => True) _raw_i20) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i20) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
  intro _raw_i20 h_2507 _
  let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_2507)
  have h_2507 : Litex.In _value_i20 (Litex.R (M := M)) := h_2507
  let _composition_call := (let _object_w34 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w34 (h_112 (M := M)) (by
  let _atomic_wd_1_0 := _object_w34
  exact (by
    let _litex_return_call := _object_w34
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) _value_i19 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i20 : M.Value) => True) (fun (_raw_i20 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i20))) (by
  intro _raw_i20 h_2507 _
  let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_2507)
  have h_2507 : Litex.In _value_i20 (Litex.R (M := M)) := h_2507
  change (by
    let _atomic_wd_1_0 := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w35 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w35
      exact (by
        let _litex_return_call := _object_w35
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w35 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w35
      exact (by
        let _litex_return_call := _object_w35
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i20 : M.Value), M.mem _raw_i20 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i20 : M.Value) => True) _raw_i20) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i20) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
  intro _raw_i20 h_2507 _
  let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_2507)
  have h_2507 : Litex.In _value_i20 (Litex.R (M := M)) := h_2507
  let _composition_call := (let _object_w34 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i20 (h_112 (M := M)) h_2507 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w34 (h_112 (M := M)) (by
  let _atomic_wd_1_0 := _object_w34
  exact (by
    let _litex_return_call := _object_w34
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) h_2493 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w36 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w36
  exact (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i21 : M.Value) => True))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i21 : M.Value) => True))).output (Litex.denote (_object_w36).val.function) (Litex.denote _value_i19) (Litex.composeInFnSet (_object_w36).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i21 : M.Value) => True) (Litex.denote _value_i19)).mpr ⟨h_2493, True.intro⟩))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro))

theorem h_337 : (by
  let _equal_wd_1_0 := (_object_w52 (M := M))
  let _equal_wd_1_1 := (_object_w53 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w52 (M := M));
        let _equal_wd_1_1 := (_object_w53 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.FunctionSemantics.composition_associative (Litex.composeSpec (_equal_wd_1_0).val.outer) (Litex.composeSpec (_equal_wd_1_1).val.inner) (Litex.composeSpec _equal_wd_1_0) (Litex.composeSpec _equal_wd_1_1))))
      )
  )

noncomputable def _object_i30 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (fun (_raw_i31 : M.Value) => _raw_i31) (by
  intro _raw_i31 h_3666 _
  let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_3666)
  have h_3666 : Litex.In _value_i31 (Litex.R (M := M)) := h_3666
  change Litex.In _value_i31 (Litex.R (M := M))
  exact h_3666))
theorem h_3673 : Litex.In (_object_i30 (M := M)) (Litex.fnSet ((_object_i30 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i30 (M := M)))
      )
  )
theorem h_3674 : Litex.Same (_object_i30 (M := M)) (_object_i30 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i30 (M := M)))
      )
  )

noncomputable def _object_w62 := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i32 : M.Value) (_raw_i33 : M.Value) => (∃ (_r _s : ℝ), _raw_i32 = M.number (_r : ℂ) ∧ _raw_i33 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i32 : M.Value) (_raw_i33 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i30 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i32, _raw_i33])))) (by
  intro _raw_i32 _raw_i33 h_3736 h_3737 h_3676
  let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_3736)
  have h_3736 : Litex.In _value_i32 (Litex.R (M := M)) := h_3736
  let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_3737)
  have h_3737 : Litex.In _value_i33 (Litex.R (M := M)) := h_3737
  have h_3676 : Litex.Lt _value_i32 _value_i33 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i32 = M.number (_r : ℂ) ∧ _raw_i33 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_3676)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w61 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i32 _value_i33 (h_335 (M := M)) h_3736 h_3737 h_3676);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _object_w61 (h_3673 (M := M)) (by
      let _atomic_wd_2_0 := _object_w61
      exact (by
        let _litex_return_call := _object_w61
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w61 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i32 _value_i33 (h_335 (M := M)) h_3736 h_3737 h_3676);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _object_w61 (h_3673 (M := M)) (by
      let _atomic_wd_2_0 := _object_w61
      exact (by
        let _litex_return_call := _object_w61
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i30 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i30 (M := M)) (_object_i30 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) ((h_3674 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i30 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i32 : M.Value) (_raw_i33 : M.Value), M.mem _raw_i32 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i33 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i32 : M.Value) (_raw_i33 : M.Value) => (∃ (_r _s : ℝ), _raw_i32 = M.number (_r : ℂ) ∧ _raw_i33 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i32 _raw_i33) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i32, _raw_i33])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))).domain := (by
  intro _raw_i32 _raw_i33 h_3736 h_3737 h_3676
  let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_3736)
  have h_3736 : Litex.In _value_i32 (Litex.R (M := M)) := h_3736
  let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_3737)
  have h_3737 : Litex.In _value_i33 (Litex.R (M := M)) := h_3737
  have h_3676 : Litex.Lt _value_i32 _value_i33 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i32 = M.number (_r : ℂ) ∧ _raw_i33 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_3676)
        )
    )
  let _composition_call := (let _object_w60 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i32 _value_i33 (h_335 (M := M)) h_3736 h_3737 h_3676);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _object_w60 (h_3673 (M := M)) (by
  let _atomic_wd_1_0 := _object_w60
  exact (by
    let _litex_return_call := _object_w60
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True)) (Litex.inOfSame (_object_i30 (M := M)) (_object_i30 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) ((h_3674 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i30 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
  have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
  have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
))
  have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
  apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
  apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
  funext i
  fin_cases i <;> norm_num [Litex.FiniteFunction.index])
  simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0)))

theorem h_3675 : (by
  let _equal_wd_1_0 := (_object_w62 (M := M))
  exact Litex.Same _equal_wd_1_0 (_object_i5 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w62 (M := M));
        (show Litex.Same _equal_wd_1_0 (_object_i5 (M := M)) from (Litex.composeLeftIdentity _equal_wd_1_0 (_object_i30 (M := M)) (h_3674 (M := M)) (by intro x; rfl))))
      )
  )

noncomputable def _object_w66 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i36 : M.Value) => True) (fun (_raw_i36 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i30 (M := M))) _raw_i36))) (by
  intro _raw_i36 h_4193 _
  let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_4193)
  have h_4193 : Litex.In _value_i36 (Litex.R (M := M)) := h_4193
  change (by
    let _atomic_wd_1_0 := (let _object_w65 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _value_i36 (h_3673 (M := M)) h_4193 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w65 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w65
      exact (by
        let _litex_return_call := _object_w65
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w65 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _value_i36 (h_3673 (M := M)) h_4193 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w65 (h_112 (M := M)) (by
      let _atomic_wd_2_0 := _object_w65
      exact (by
        let _litex_return_call := _object_w65
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i3 (M := M)) (_object_i30 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.inOfSame (_object_i30 (M := M)) (_object_i30 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True))) ((h_3674 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i30 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i36 : M.Value), M.mem _raw_i36 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i36 : M.Value) => True) _raw_i36) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i30 (M := M))) _raw_i36) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))).domain := (by
  intro _raw_i36 h_4193 _
  let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_4193)
  have h_4193 : Litex.In _value_i36 (Litex.R (M := M)) := h_4193
  let _composition_call := (let _object_w64 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) => True) (_object_i30 (M := M)) _value_i36 (h_3673 (M := M)) h_4193 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w64 (h_112 (M := M)) (by
  let _atomic_wd_1_0 := _object_w64
  exact (by
    let _litex_return_call := _object_w64
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro))

theorem h_4179 : (by
  let _equal_wd_1_0 := (_object_w66 (M := M))
  exact Litex.Same _equal_wd_1_0 (_object_i3 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w66 (M := M));
        (show Litex.Same _equal_wd_1_0 (_object_i3 (M := M)) from (Litex.composeRightIdentity _equal_wd_1_0 (_object_i30 (M := M)) (h_3674 (M := M)) (by intro x; rfl) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by rfl))))
      )
  )

noncomputable def _object_w79 := (let _wd_1_0 := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])))) (by
  intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
  let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
  have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
  let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
  have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
  have h_4527 : Litex.Lt _value_i37 _value_i38 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_4527)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w70
      exact (by
        let _litex_return_call := _object_w70
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w70
      exact (by
        let _litex_return_call := _object_w70
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i37 : M.Value) (_raw_i38 : M.Value), M.mem _raw_i37 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i38 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i37 _raw_i38) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
  let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
  have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
  let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
  have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
  have h_4527 : Litex.Lt _value_i37 _value_i38 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_4527)
        )
    )
  let _composition_call := (let _object_w69 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w69 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w69
  exact (by
    let _litex_return_call := _object_w69
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
  have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
  have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
))
  have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
  apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
  apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
  funext i
  fin_cases i <;> norm_num [Litex.FiniteFunction.index])
  simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0)));
(by
  have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s)))) := (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i41, _raw_i42])))) (by
  intro _raw_i41 _raw_i42 h_5089 h_5090 h_5029
  let _value_i41 := Litex.semanticObject (M := M) _raw_i41 (M.member_isSet h_5089)
  have h_5089 : Litex.In _value_i41 (Litex.R (M := M)) := h_5089
  let _value_i42 := Litex.semanticObject (M := M) _raw_i42 (M.member_isSet h_5090)
  have h_5090 : Litex.In _value_i42 (Litex.R (M := M)) := h_5090
  have h_5029 : Litex.Lt _value_i41 _value_i42 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_5029)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w74 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i41 _value_i42 (h_335 (M := M)) h_5089 h_5090 h_5029);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w74 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w74
      exact (by
        let _litex_return_call := _object_w74
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w74 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i41 _value_i42 (h_335 (M := M)) h_5089 h_5090 h_5029);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w74 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w74
      exact (by
        let _litex_return_call := _object_w74
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i41 : M.Value) (_raw_i42 : M.Value), M.mem _raw_i41 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i42 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i41 _raw_i42) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i41, _raw_i42])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i41 _raw_i42 h_5089 h_5090 h_5029
  let _value_i41 := Litex.semanticObject (M := M) _raw_i41 (M.member_isSet h_5089)
  have h_5089 : Litex.In _value_i41 (Litex.R (M := M)) := h_5089
  let _value_i42 := Litex.semanticObject (M := M) _raw_i42 (M.member_isSet h_5090)
  have h_5090 : Litex.In _value_i42 (Litex.R (M := M)) := h_5090
  have h_5029 : Litex.Lt _value_i41 _value_i42 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_5029)
        )
    )
  let _composition_call := (let _object_w73 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i41 _value_i42 (h_335 (M := M)) h_5089 h_5090 h_5029);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w73 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w73
  exact (by
    let _litex_return_call := _object_w73
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
  have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
  have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
))
  have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
  apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
  apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
  funext i
  fin_cases i <;> norm_num [Litex.FiniteFunction.index])
  simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))))
  exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (∃ (_r _s : ℝ), _raw_i41 = M.number (_r : ℂ) ∧ _raw_i42 = M.number (_s : ℂ) ∧ _r < _s))) _range_signature_0))

noncomputable def _object_w80 := (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_42 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_42)
    have h_42 : Litex.In _value_i2 (Litex.R (M := M)) := h_42
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_43 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) _range_signature_0)

theorem h_4526 : (by
  let _atomic_wd_1_0 := (_object_w79 (M := M))
  let _atomic_wd_1_1 := (_object_w80 (M := M))
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w79 (M := M))
          let _atomic_wd_1_1 := (_object_w80 (M := M))
          exact (by
            have _composition_interface := (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])))) (by
            intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
            let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
            have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
            let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
            have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
            have h_4527 : Litex.Lt _value_i37 _value_i38 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_4527)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w70
                exact (by
                  let _litex_return_call := _object_w70
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w70
                exact (by
                  let _litex_return_call := _object_w70
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i37 : M.Value) (_raw_i38 : M.Value), M.mem _raw_i37 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i38 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i37 _raw_i38) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
            let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
            have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
            let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
            have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
            have h_4527 : Litex.Lt _value_i37 _value_i38 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_4527)
                  )
              )
            let _composition_call := (let _object_w69 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w69 (h_43 (M := M)) (by
            let _atomic_wd_2_0 := _object_w69
            exact (by
              let _litex_return_call := _object_w69
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index])
            simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))))
            exact Litex.composeRangeSubset (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])))) (by
            intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
            let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
            have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
            let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
            have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
            have h_4527 : Litex.Lt _value_i37 _value_i38 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_4527)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w70
                exact (by
                  let _litex_return_call := _object_w70
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w70 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w70 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w70
                exact (by
                  let _litex_return_call := _object_w70
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i37 : M.Value) (_raw_i38 : M.Value), M.mem _raw_i37 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i38 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i37 _raw_i38) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i37, _raw_i38])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i37 _raw_i38 h_4587 h_4588 h_4527
            let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_4587)
            have h_4587 : Litex.In _value_i37 (Litex.R (M := M)) := h_4587
            let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_4588)
            have h_4588 : Litex.In _value_i38 (Litex.R (M := M)) := h_4588
            have h_4527 : Litex.Lt _value_i37 _value_i38 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i37 = M.number (_r : ℂ) ∧ _raw_i38 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_4527)
                  )
              )
            let _composition_call := (let _object_w69 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i37 _value_i38 (h_335 (M := M)) h_4587 h_4588 h_4527);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w69 (h_43 (M := M)) (by
            let _atomic_wd_2_0 := _object_w69
            exact (by
              let _litex_return_call := _object_w69
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
            have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
            have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          ))
            have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
            apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index])
            simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0))) _atomic_wd_1_0 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by rfl)))
      )
  )

noncomputable def _object_w87 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i55 : M.Value) => True) (fun (_raw_i55 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i55))) (by
  intro _raw_i55 h_6017 _
  let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_6017)
  have h_6017 : Litex.In _value_i55 (Litex.R (M := M)) := h_6017
  change (by
    let _atomic_wd_1_0 := (let _object_w83 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i55 (h_112 (M := M)) h_6017 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w83 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w83
      exact (by
        let _litex_return_call := _object_w83
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w83 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i55 (h_112 (M := M)) h_6017 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w83 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w83
      exact (by
        let _litex_return_call := _object_w83
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i55 : M.Value), M.mem _raw_i55 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i55 : M.Value) => True) _raw_i55) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i55) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i55 h_6017 _
  let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_6017)
  have h_6017 : Litex.In _value_i55 (Litex.R (M := M)) := h_6017
  let _composition_call := (let _object_w82 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i55 (h_112 (M := M)) h_6017 True.intro);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w82 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w82
  exact (by
    let _litex_return_call := _object_w82
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _preimage_domain
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members True.intro))

noncomputable def _object_w88 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i54 : M.Value) => True) (fun (_raw_i54 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i54))) (by
  intro _raw_i54 h_6368 _
  let _value_i54 := Litex.semanticObject (M := M) _raw_i54 (M.member_isSet h_6368)
  have h_6368 : Litex.In _value_i54 (Litex.R (M := M)) := h_6368
  change (by
    let _atomic_wd_1_0 := (let _object_w86 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i54 (h_112 (M := M)) h_6368 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w86 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w86
      exact (by
        let _litex_return_call := _object_w86
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w86 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i54 (h_112 (M := M)) h_6368 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w86 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w86
      exact (by
        let _litex_return_call := _object_w86
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

theorem h_6003 : (by
  let _equal_wd_1_0 := (_object_w87 (M := M))
  let _equal_wd_1_1 := (_object_w88 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w87 (M := M));
        let _equal_wd_1_1 := (_object_w88 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          have _composition_interface := (Litex.composeInFnSet _equal_wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
          have _composition_formula : Litex.Same _equal_wd_1_0 _equal_wd_1_1 := (Litex.composeEqFormula _equal_wd_1_0 _equal_wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by rfl) (by intro x _; rfl))
          exact _composition_formula.trans (show Litex.Same _equal_wd_1_1 _equal_wd_1_1 from ((show @Eq M.Value _ _ from Eq.refl _)).symm))))
      )
  )

noncomputable def _object_w92 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i58 : M.Value) => True) (fun (_raw_i58 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i58))) (by
  intro _raw_i58 h_6721 _
  let _value_i58 := Litex.semanticObject (M := M) _raw_i58 (M.member_isSet h_6721)
  have h_6721 : Litex.In _value_i58 (Litex.R (M := M)) := h_6721
  change (by
    let _atomic_wd_1_0 := (let _object_w91 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i58 (h_112 (M := M)) h_6721 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w91 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w91
      exact (by
        let _litex_return_call := _object_w91
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w91 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i58 (h_112 (M := M)) h_6721 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w91 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w91
      exact (by
        let _litex_return_call := _object_w91
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))

theorem h_6707 : (by
  let _equal_wd_1_0 := (_object_w87 (M := M))
  let _equal_wd_1_1 := (_object_w92 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w87 (M := M));
        let _equal_wd_1_1 := (_object_w92 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          have _composition_interface := (Litex.composeInFnSet _equal_wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
          have _composition_formula : Litex.Same _equal_wd_1_0 _equal_wd_1_1 := (Litex.composeEqFormula _equal_wd_1_0 _equal_wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_113 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by rfl) (by intro x _; rfl))
          exact _composition_formula.trans (show Litex.Same _equal_wd_1_1 _equal_wd_1_1 from ((show @Eq M.Value _ _ from Eq.refl _)).symm))))
      )
  )

noncomputable def _object_w101 := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => (∃ (_r _s : ℝ), _raw_i63 = M.number (_r : ℂ) ∧ _raw_i64 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i63, _raw_i64])))) (by
  intro _raw_i63 _raw_i64 h_7131 h_7132 h_7071
  let _value_i63 := Litex.semanticObject (M := M) _raw_i63 (M.member_isSet h_7131)
  have h_7131 : Litex.In _value_i63 (Litex.R (M := M)) := h_7131
  let _value_i64 := Litex.semanticObject (M := M) _raw_i64 (M.member_isSet h_7132)
  have h_7132 : Litex.In _value_i64 (Litex.R (M := M)) := h_7132
  have h_7071 : Litex.Lt _value_i63 _value_i64 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i63 = M.number (_r : ℂ) ∧ _raw_i64 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_7071)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w96 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i63 _value_i64 (h_335 (M := M)) h_7131 h_7132 h_7071);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w96 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w96
      exact (by
        let _litex_return_call := _object_w96
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w96 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i63 _value_i64 (h_335 (M := M)) h_7131 h_7132 h_7071);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w96 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w96
      exact (by
        let _litex_return_call := _object_w96
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i63 : M.Value) (_raw_i64 : M.Value), M.mem _raw_i63 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i64 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => (∃ (_r _s : ℝ), _raw_i63 = M.number (_r : ℂ) ∧ _raw_i64 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i63 _raw_i64) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i63, _raw_i64])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i63 _raw_i64 h_7131 h_7132 h_7071
  let _value_i63 := Litex.semanticObject (M := M) _raw_i63 (M.member_isSet h_7131)
  have h_7131 : Litex.In _value_i63 (Litex.R (M := M)) := h_7131
  let _value_i64 := Litex.semanticObject (M := M) _raw_i64 (M.member_isSet h_7132)
  have h_7132 : Litex.In _value_i64 (Litex.R (M := M)) := h_7132
  have h_7071 : Litex.Lt _value_i63 _value_i64 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i63 = M.number (_r : ℂ) ∧ _raw_i64 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_7071)
        )
    )
  let _composition_call := (let _object_w95 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i63 _value_i64 (h_335 (M := M)) h_7131 h_7132 h_7071);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w95 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w95
  exact (by
    let _litex_return_call := _object_w95
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
  have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
  have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
))
  have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
  apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
  apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
  funext i
  fin_cases i <;> norm_num [Litex.FiniteFunction.index])
  simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0)))

noncomputable def _object_w102 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i61 : M.Value) (_raw_i62 : M.Value) => (∃ (_r _s : ℝ), _raw_i61 = M.number (_r : ℂ) ∧ _raw_i62 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i61 : M.Value) (_raw_i62 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i61, _raw_i62])))) (by
  intro _raw_i61 _raw_i62 h_7638 h_7639 h_7069
  let _value_i61 := Litex.semanticObject (M := M) _raw_i61 (M.member_isSet h_7638)
  have h_7638 : Litex.In _value_i61 (Litex.R (M := M)) := h_7638
  let _value_i62 := Litex.semanticObject (M := M) _raw_i62 (M.member_isSet h_7639)
  have h_7639 : Litex.In _value_i62 (Litex.R (M := M)) := h_7639
  have h_7069 : Litex.Lt _value_i61 _value_i62 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i61 = M.number (_r : ℂ) ∧ _raw_i62 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_7069)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w100 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i61 _value_i62 (h_335 (M := M)) h_7638 h_7639 h_7069);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w100 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w100
      exact (by
        let _litex_return_call := _object_w100
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w100 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i61 _value_i62 (h_335 (M := M)) h_7638 h_7639 h_7069);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w100 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w100
      exact (by
        let _litex_return_call := _object_w100
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

theorem h_7070 : (by
  let _equal_wd_1_0 := (_object_w101 (M := M))
  let _equal_wd_1_1 := (_object_w102 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w101 (M := M));
        let _equal_wd_1_1 := (_object_w102 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          have _composition_interface := (Litex.composeInFnSet _equal_wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))))
          have _composition_formula : Litex.Same _equal_wd_1_0 _equal_wd_1_1 := (Litex.composeEqFormula _equal_wd_1_0 _equal_wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_336 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (by rfl) (by
          intro _composition_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), _raw_i6 = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _composition_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ)))] := (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index])
          exact congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) x)) _repack.symm))
          exact _composition_formula.trans (show Litex.Same _equal_wd_1_1 _equal_wd_1_1 from ((show @Eq M.Value _ _ from Eq.refl _)).symm))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_composition_x5f_graph_x5f_laws_x2f_statement_x2e_lit
