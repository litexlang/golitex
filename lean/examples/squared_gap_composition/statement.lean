import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_squared_x5f_gap_x5f_composition_x2f_statement_x2e_lit

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

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (by
  intro _raw_i4 _raw_i5 h_105 h_106 h_45
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_105)
  have h_105 : Litex.In _value_i4 (Litex.R (M := M)) := h_105
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_106)
  have h_106 : Litex.In _value_i5 (Litex.R (M := M)) := h_106
  have h_45 : Litex.Lt _value_i4 _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_45)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i4 (M.real_subset_complex _ h_106) (M.real_subset_complex _ h_105))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i4 (M.real_subset_complex _ h_106) (M.real_subset_complex _ h_105))
    exact (Litex.subInR _value_i5 _value_i4 h_106 h_105))))
theorem h_246 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_247 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_i8 := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i11, _raw_i12])))) (by
  intro _raw_i11 _raw_i12 h_339 h_340 h_279
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_339)
  have h_339 : Litex.In _value_i11 (Litex.R (M := M)) := h_339
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_340)
  have h_340 : Litex.In _value_i12 (Litex.R (M := M)) := h_340
  have h_279 : Litex.Lt _value_i11 _value_i12 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_279)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w15 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w15 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        let _litex_return_call := _object_w15
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w15 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w15 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        let _litex_return_call := _object_w15
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i11 : M.Value) (_raw_i12 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i11 _raw_i12) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i11, _raw_i12])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  intro _raw_i11 _raw_i12 h_339 h_340 h_279
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_339)
  have h_339 : Litex.In _value_i11 (Litex.R (M := M)) := h_339
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_340)
  have h_340 : Litex.In _value_i12 (Litex.R (M := M)) := h_340
  have h_279 : Litex.Lt _value_i11 _value_i12 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_279)
        )
    )
  let _composition_call := (let _object_w14 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w14 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w14
  exact (by
    let _litex_return_call := _object_w14
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
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
theorem h_1100 : Litex.In (_object_i8 (M := M)) (let _checked_header : ∀ (_raw_i9 : M.Value) (_raw_i10 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i9 _raw_i10) → True := (by
    intro _raw_i9 _raw_i10 h_1061 h_1062 h_669
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1061)
    have h_1061 : Litex.In _value_i9 (Litex.R (M := M)) := h_1061
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1062)
    have h_1062 : Litex.In _value_i10 (Litex.R (M := M)) := h_1062
    have h_669 : Litex.Lt _value_i9 _value_i10 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s)
              exact h_669)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (∃ (_r _s : ℝ), _raw_i15 = M.number (_r : ℂ) ∧ _raw_i16 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i16])))) (by
            intro _raw_i15 _raw_i16 h_731 h_732 h_671
            let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_731)
            have h_731 : Litex.In _value_i15 (Litex.R (M := M)) := h_731
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_732)
            have h_732 : Litex.In _value_i16 (Litex.R (M := M)) := h_732
            have h_671 : Litex.Lt _value_i15 _value_i16 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i15 = M.number (_r : ℂ) ∧ _raw_i16 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_671)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w19 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i15 _value_i16 (h_246 (M := M)) h_731 h_732 h_671);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w19 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i15 _value_i16 (h_246 (M := M)) h_731 h_732 h_671);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w19 (h_43 (M := M)) (by
                let _atomic_wd_3_0 := _object_w19
                exact (by
                  let _litex_return_call := _object_w19
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (∃ (_r _s : ℝ), _raw_i15 = M.number (_r : ℂ) ∧ _raw_i16 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i15 _raw_i16) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i16])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            intro _raw_i15 _raw_i16 h_731 h_732 h_671
            let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_731)
            have h_731 : Litex.In _value_i15 (Litex.R (M := M)) := h_731
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_732)
            have h_732 : Litex.In _value_i16 (Litex.R (M := M)) := h_732
            have h_671 : Litex.Lt _value_i15 _value_i16 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (∃ (_r _s : ℝ), _raw_i15 = M.number (_r : ℂ) ∧ _raw_i16 = M.number (_s : ℂ) ∧ _r < _s)
                      exact h_671)
                  )
              )
            let _composition_call := (let _object_w18 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i15 _value_i16 (h_246 (M := M)) h_731 h_732 h_671);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w18 (h_43 (M := M)) (by
            let _atomic_wd_2_0 := _object_w18
            exact (by
              let _litex_return_call := _object_w18
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
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
          let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i9 : M.Value) (_raw_i10 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i9 _raw_i10) → True := (by
              intro _raw_i9 _raw_i10 h_1061 h_1062 h_669
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1061)
              have h_1061 : Litex.In _value_i9 (Litex.R (M := M)) := h_1061
              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1062)
              have h_1062 : Litex.In _value_i10 (Litex.R (M := M)) := h_1062
              have h_669 : Litex.Lt _value_i9 _value_i10 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_669)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (∃ (_r _s : ℝ), _raw_i9 = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r < _s))))
          exact (Litex.composeInFnSet _atomic_wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))))
      )
  )
theorem h_1101 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i11, _raw_i12])))) (by
          intro _raw_i11 _raw_i12 h_339 h_340 h_279
          let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_339)
          have h_339 : Litex.In _value_i11 (Litex.R (M := M)) := h_339
          let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_340)
          have h_340 : Litex.In _value_i12 (Litex.R (M := M)) := h_340
          have h_279 : Litex.Lt _value_i11 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)
                    exact h_279)
                )
            )
          change (by
            let _atomic_wd_1_0 := (let _object_w15 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w15 (h_43 (M := M)) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _object_w15 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w15 (h_43 (M := M)) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
        Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
          have _composition_checked : ∀ (_raw_i11 : M.Value) (_raw_i12 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i11 _raw_i12) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i11, _raw_i12])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
          intro _raw_i11 _raw_i12 h_339 h_340 h_279
          let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_339)
          have h_339 : Litex.In _value_i11 (Litex.R (M := M)) := h_339
          let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_340)
          have h_340 : Litex.In _value_i12 (Litex.R (M := M)) := h_340
          have h_279 : Litex.Lt _value_i11 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (∃ (_r _s : ℝ), _raw_i11 = M.number (_r : ℂ) ∧ _raw_i12 = M.number (_s : ℂ) ∧ _r < _s)
                    exact h_279)
                )
            )
          let _composition_call := (let _object_w14 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) _value_i11 _value_i12 (h_246 (M := M)) h_339 h_340 h_279);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w14 (h_43 (M := M)) (by
          let _atomic_wd_1_0 := _object_w14
          exact (by
            let _litex_return_call := _object_w14
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
          intro _composition_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
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
          simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0))))
      )
  )

noncomputable def _object_w25 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => (∃ (_r _s : ℝ), _raw_i23 = M.number (_r : ℂ) ∧ _raw_i24 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i8 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.inOfSame (_object_i8 (M := M)) (_object_i8 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => (∃ (_r _s : ℝ), _raw_i23 = M.number (_r : ℂ) ∧ _raw_i24 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => (∃ (_r _s : ℝ), _raw_i23 = M.number (_r : ℂ) ∧ _raw_i24 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_1101 (M := M))).symm (Litex.sameRefl _) (Litex.composeInFnSet (_object_i8 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_1102 : (by
  let _equal_wd_1_0 := (_object_w25 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])) = (M.number (4 : ℂ)) from by
          have _litex_residual : (M.powValue (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) (M.number (2 : ℂ))) = (M.number (4 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) - (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (4 : ℂ)) (((3 : ℂ) - (1 : ℂ)) ^ (2 : ℕ)) (4 : ℂ) (Litex.NativeBridge.denotePowNatReal (_equal_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := (_equal_wd_2_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) - (1 : ℂ)) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.base).wd.1 ((_equal_wd_2_0).val.base).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num))))
          exact ((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))]))) from by
          have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ))))) (show (Litex.denote (_object_i8 (M := M))) = Litex.denote (_object_i8 (M := M)) from (h_1101 (M := M)))
          exact _composition_head.trans (Litex.composeCall (_object_i8 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ)))) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => (∃ (_r _s : ℝ), _raw_i29 = M.number (_r : ℂ) ∧ _raw_i30 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))⟩))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])) = (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_246 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_247 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from rfl))
        )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ)))) = (M.powValue (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) (M.number (2 : ℂ))) from by
          let _litex_original := (let _object_w23 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w23 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _object_w23
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w23).wd.1 (_object_w23).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) - (1 : ℂ)) (2 : ℝ) (by norm_num)))) True.intro))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w24 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w24 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w24
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w24).wd.1 (_object_w24).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) - (1 : ℂ)) (2 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.subValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)
      )
  )

noncomputable def _object_w27 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => (∃ (_r _s : ℝ), _raw_i31 = M.number (_r : ℂ) ∧ _raw_i32 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i8 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.composeInFnSet (_object_i8 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_1375 : (by
  let _equal_wd_1_0 := (_object_w27 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (show @Eq M.Value _ _ from Eq.refl _) (Eq.trans (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) ((h_1101 (M := M))).symm (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (show @Eq M.Value _ _ from Eq.refl _))) (h_1102 (M := M))))
      )
  )

noncomputable def _object_w38 := (let _object_w28 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_246 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w28 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w28
  exact (by
    let _litex_return_call := _object_w28
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))

theorem h_1512 : (by
  let _equal_wd_1_0 := (_object_w27 (M := M))
  let _equal_wd_1_1 := (_object_w38 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_object_w27 (M := M))).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))]))) from by
          have _litex_residual : (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))]))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))]))) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_object_w27 (M := M))).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_object_w27 (M := M))).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (3 : ℂ))]))) from by
          have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ))))) (show (Litex.denote ((_object_w27 (M := M))).val.function) = Litex.denote ((_object_w27 (M := M))).val.function from (show @Eq M.Value _ _ from Eq.refl _))
          exact _composition_head.trans (Litex.composeCall ((_object_w27 (M := M))).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ)))) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => (∃ (_r _s : ℝ), _raw_i31 = M.number (_r : ℂ) ∧ _raw_i32 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))⟩))))).trans _litex_residual)
      )
  )

noncomputable def _object_w41 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i39 : M.Value) (_raw_i40 : M.Value) => (∃ (_r _s : ℝ), _raw_i39 = M.number (_r : ℂ) ∧ _raw_i40 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.inOfSame (_object_i8 (M := M)) (_object_i8 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i39 : M.Value) (_raw_i40 : M.Value) => (∃ (_r _s : ℝ), _raw_i39 = M.number (_r : ℂ) ∧ _raw_i40 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i39 : M.Value) (_raw_i40 : M.Value) => (∃ (_r _s : ℝ), _raw_i39 = M.number (_r : ℂ) ∧ _raw_i40 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_1101 (M := M))).symm (Litex.sameRefl _) (Litex.composeInFnSet (_object_i8 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_2501 : (by
  let _equal_wd_1_0 := (_object_w41 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (5 : ℂ))])) = (M.number (9 : ℂ)) from by
          have _litex_residual : (M.powValue (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.number (9 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) - (2 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) (((5 : ℂ) - (2 : ℂ)) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (_equal_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := (_equal_wd_2_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) - (2 : ℂ)) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.base).wd.1 ((_equal_wd_2_0).val.base).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))))
          exact ((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (5 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (5 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (5 : ℂ))]))) from by
          have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (5 : ℂ))))) (show (Litex.denote (_object_i8 (M := M))) = Litex.denote (_object_i8 (M := M)) from (h_1101 (M := M)))
          exact _composition_head.trans (Litex.composeCall (_object_i8 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_247 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (5 : ℂ)))) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i45 : M.Value) (_raw_i46 : M.Value) => (∃ (_r _s : ℝ), _raw_i45 = M.number (_r : ℂ) ∧ _raw_i46 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (5 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))⟩))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (5 : ℂ))])) = (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (h_246 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal _wd_1_1 _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_2 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_247 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (∃ (_r _s : ℝ), _raw_i4 = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r < _s)) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i5 _raw_i4)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) from rfl))
        )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ)))) = (M.powValue (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
          let _litex_original := (let _object_w39 := (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _object_w39
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w39).wd.1 (_object_w39).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) - (2 : ℂ)) (3 : ℝ) (by norm_num)))) True.intro))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w40 := (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w40 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w40
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w40).wd.1 (_object_w40).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) - (2 : ℂ)) (3 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_squared_x5f_gap_x5f_composition_x2f_statement_x2e_lit
