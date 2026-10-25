import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_composed_x5f_quotient_x5f_membership_x2f_statement_x2e_lit

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

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 _raw_i5)) (by
  rintro _raw_i4 _raw_i5 h_120 h_121 ⟨h_45, h_46⟩
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_120)
  have h_120 : Litex.In _value_i4 (Litex.R (M := M)) := h_120
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_121)
  have h_121 : Litex.In _value_i5 (Litex.R (M := M)) := h_121
  have h_45 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i5 = (M.number (0 : ℂ))))
            exact h_45)
        )
    )
  have h_46 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
            exact h_46)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_120) (M.real_subset_complex _ h_121) h_45)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_120) (M.real_subset_complex _ h_121) h_45)
    exact (Litex.divInR _value_i4 _value_i5 h_120 h_121 (_atomic_wd_1_0).wd.2.2))))
theorem h_223 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_224 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_227 : Litex.In (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i44 : M.Value) (_raw_i45 : M.Value) => (((¬ (_raw_i45 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i44 = (M.number (0 : ℂ))))))) (fun (_raw_i44 : M.Value) (_raw_i45 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i44, _raw_i45])))) (by
  rintro _raw_i44 _raw_i45 h_2223 h_2224 ⟨h_2148, h_2149⟩
  let _value_i44 := Litex.semanticObject (M := M) _raw_i44 (M.member_isSet h_2223)
  have h_2223 : Litex.In _value_i44 (Litex.R (M := M)) := h_2223
  let _value_i45 := Litex.semanticObject (M := M) _raw_i45 (M.member_isSet h_2224)
  have h_2224 : Litex.In _value_i45 (Litex.R (M := M)) := h_2224
  have h_2148 : ¬ Litex.Same _value_i45 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i45 = (M.number (0 : ℂ))))
            exact h_2148)
        )
    )
  have h_2149 : ¬ Litex.Same _value_i44 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i44 = (M.number (0 : ℂ))))
            exact h_2149)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w60 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i44 _value_i45 (h_223 (M := M)) h_2223 h_2224 (And.intro h_2148 h_2149));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w60 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w60
      exact (by
        let _litex_return_call := _object_w60
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w60 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i44 _value_i45 (h_223 (M := M)) h_2223 h_2224 (And.intro h_2148 h_2149));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w60 (h_43 (M := M)) (by
      let _atomic_wd_2_0 := _object_w60
      exact (by
        let _litex_return_call := _object_w60
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i44 : M.Value) (_raw_i45 : M.Value), M.mem _raw_i44 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i45 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i44 : M.Value) (_raw_i45 : M.Value) => (((¬ (_raw_i45 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i44 = (M.number (0 : ℂ))))))) _raw_i44 _raw_i45) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i44, _raw_i45])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
  rintro _raw_i44 _raw_i45 h_2223 h_2224 ⟨h_2148, h_2149⟩
  let _value_i44 := Litex.semanticObject (M := M) _raw_i44 (M.member_isSet h_2223)
  have h_2223 : Litex.In _value_i44 (Litex.R (M := M)) := h_2223
  let _value_i45 := Litex.semanticObject (M := M) _raw_i45 (M.member_isSet h_2224)
  have h_2224 : Litex.In _value_i45 (Litex.R (M := M)) := h_2224
  have h_2148 : ¬ Litex.Same _value_i45 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i45 = (M.number (0 : ℂ))))
            exact h_2148)
        )
    )
  have h_2149 : ¬ Litex.Same _value_i44 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i44 = (M.number (0 : ℂ))))
            exact h_2149)
        )
    )
  let _composition_call := (let _object_w59 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i44 _value_i45 (h_223 (M := M)) h_2223 h_2224 (And.intro h_2148 h_2149));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w59 (h_43 (M := M)) (by
  let _atomic_wd_1_0 := _object_w59
  exact (by
    let _litex_return_call := _object_w59
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
  rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
  simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) (let _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))) _raw_i10 _raw_i11) → True := (by
    rintro _raw_i10 _raw_i11 h_2541 h_2542 ⟨h_225, h_226⟩
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_2541)
    have h_2541 : Litex.In _value_i10 (Litex.R (M := M)) := h_2541
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_2542)
    have h_2542 : Litex.In _value_i11 (Litex.R (M := M)) := h_2542
    have h_225 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i10 = (M.number (0 : ℂ))))
              exact h_225)
          )
      )
    have h_226 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i11 = (M.number (0 : ℂ))))
              exact h_226)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => (((¬ (_raw_i13 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i12 = (M.number (0 : ℂ))))))) (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])))) (by
            rintro _raw_i12 _raw_i13 h_305 h_306 ⟨h_230, h_231⟩
            let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_305)
            have h_305 : Litex.In _value_i12 (Litex.R (M := M)) := h_305
            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_306)
            have h_306 : Litex.In _value_i13 (Litex.R (M := M)) := h_306
            have h_230 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i13 = (M.number (0 : ℂ))))
                      exact h_230)
                  )
              )
            have h_231 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i12 = (M.number (0 : ℂ))))
                      exact h_231)
                  )
              )
            change (by
              let _atomic_wd_1_0 := (let _object_w22 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i12 _value_i13 (h_223 (M := M)) h_305 h_306 (And.intro h_230 h_231));
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
                let _atomic_wd_2_0 := _object_w22
                exact (by
                  let _litex_return_call := _object_w22
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _object_w22 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i12 _value_i13 (h_223 (M := M)) h_305 h_306 (And.intro h_230 h_231));
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w22 (h_43 (M := M)) (by
                let _atomic_wd_2_0 := _object_w22
                exact (by
                  let _litex_return_call := _object_w22
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i12 : M.Value) (_raw_i13 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i13 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => (((¬ (_raw_i13 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i12 = (M.number (0 : ℂ))))))) _raw_i12 _raw_i13) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
            rintro _raw_i12 _raw_i13 h_305 h_306 ⟨h_230, h_231⟩
            let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_305)
            have h_305 : Litex.In _value_i12 (Litex.R (M := M)) := h_305
            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_306)
            have h_306 : Litex.In _value_i13 (Litex.R (M := M)) := h_306
            have h_230 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i13 = (M.number (0 : ℂ))))
                      exact h_230)
                  )
              )
            have h_231 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i12 = (M.number (0 : ℂ))))
                      exact h_231)
                  )
              )
            let _composition_call := (let _object_w21 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i12 _value_i13 (h_223 (M := M)) h_305 h_306 (And.intro h_230 h_231));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w21 (h_43 (M := M)) (by
            let _atomic_wd_1_0 := _object_w21
            exact (by
              let _litex_return_call := _object_w21
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
            rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
            simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1))))
          let _membership_target := (let _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))) _raw_i10 _raw_i11) → True := (by
              rintro _raw_i10 _raw_i11 h_623 h_624 ⟨h_225, h_226⟩
              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_623)
              have h_623 : Litex.In _value_i10 (Litex.R (M := M)) := h_623
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_624)
              have h_624 : Litex.In _value_i11 (Litex.R (M := M)) := h_624
              have h_225 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i10 = (M.number (0 : ℂ))))
                        exact h_225)
                    )
                )
              have h_226 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                        exact h_226)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ)))))))))
          have h_1025 : ∀ {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_1038 : Litex.In _value_i24 (Litex.R (M := M))) {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_1039 : Litex.In _value_i25 (Litex.R (M := M))) (h_1019 : ¬ Litex.Same _value_i25 (Litex.number (M := M) (0 : ℂ))) (h_1020 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i24 (Litex.R (M := M))) ∧ (((Litex.In _value_i25 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i25 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i24 _rep_i24 _value_i24 h_1038 _Host_i25 _rep_i25 _value_i25 h_1039 h_1019 h_1020
            have h_1021 : Litex.In _value_i24 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1038
                  )
              )
            have h_1022 : Litex.In _value_i25 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1039
                  )
              )
            have h_1023 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1020
                  )
              )
            have h_1024 : ¬ Litex.Same _value_i25 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1019
                  )
              )
            exact (And.intro h_1021 (And.intro h_1022 (And.intro h_1023 h_1024)))
          )
          have h_1067 : ∀ {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_1080 : Litex.In _value_i26 (Litex.R (M := M))) {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_1081 : Litex.In _value_i27 (Litex.R (M := M))) (h_1061 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ))) (h_1062 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i26 (Litex.R (M := M))) ∧ (((Litex.In _value_i27 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i26 _rep_i26 _value_i26 h_1080 _Host_i27 _rep_i27 _value_i27 h_1081 h_1061 h_1062
            have h_1063 : Litex.In _value_i26 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1080
                  )
              )
            have h_1064 : Litex.In _value_i27 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1081
                  )
              )
            have h_1065 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1062
                  )
              )
            have h_1066 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1061
                  )
              )
            exact (And.intro h_1063 (And.intro h_1064 (And.intro h_1065 h_1066)))
          )
          have h_228 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_1115 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_1116 : Litex.In _value_i11 (Litex.R (M := M))) (h_225 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))) (h_226 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w41 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])))) (by
              rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
              let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
              have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
              let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
              have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
              have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                        exact h_1118)
                    )
                )
              have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                        exact h_1119)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                  let _atomic_wd_2_0 := _object_w40
                  exact (by
                    let _litex_return_call := _object_w40
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                  let _atomic_wd_2_0 := _object_w40
                  exact (by
                    let _litex_return_call := _object_w40
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
            Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
              have _composition_checked : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i29 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) _raw_i28 _raw_i29) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
              rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
              let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
              have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
              let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
              have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
              have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                        exact h_1118)
                    )
                )
              have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                        exact h_1119)
                    )
                )
              let _composition_call := (let _object_w39 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
              let _atomic_wd_1_0 := _object_w39
              exact (by
                let _litex_return_call := _object_w39
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
              intro _composition_input _preimage_domain
              obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
              have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
              have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
              rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
              simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) _value_i10 _value_i11 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])))) (by
              rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
              let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
              have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
              let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
              have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
              have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                        exact h_1118)
                    )
                )
              have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                        exact h_1119)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                  let _atomic_wd_2_0 := _object_w40
                  exact (by
                    let _litex_return_call := _object_w40
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                  let _atomic_wd_2_0 := _object_w40
                  exact (by
                    let _litex_return_call := _object_w40
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
            Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
              have _composition_checked : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i29 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) _raw_i28 _raw_i29) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
              rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
              let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
              have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
              let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
              have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
              have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                        exact h_1118)
                    )
                )
              have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                        exact h_1119)
                    )
                )
              let _composition_call := (let _object_w39 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
              let _atomic_wd_1_0 := _object_w39
              exact (by
                let _litex_return_call := _object_w39
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
              exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
              intro _composition_input _preimage_domain
              obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
              have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
              have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
              rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
              simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) h_1115 h_1116 (And.intro h_226 h_225))
            exact (by
              let _atomic_wd_1_0 := _object_w41
              exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i10 _rep_i10 _value_i10 h_1115 _Host_i11 _rep_i11 _value_i11 h_1116 h_225 h_226
                    let _object_w41 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])))) (by
                      rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
                      let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
                      have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
                      have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
                      have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                                exact h_1118)
                            )
                        )
                      have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                                exact h_1119)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                          let _atomic_wd_2_0 := _object_w40
                          exact (by
                            let _litex_return_call := _object_w40
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                          let _atomic_wd_2_0 := _object_w40
                          exact (by
                            let _litex_return_call := _object_w40
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
                    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
                      have _composition_checked : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i29 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) _raw_i28 _raw_i29) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                      rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
                      let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
                      have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
                      have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
                      have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                                exact h_1118)
                            )
                        )
                      have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                                exact h_1119)
                            )
                        )
                      let _composition_call := (let _object_w39 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w39
                      exact (by
                        let _litex_return_call := _object_w39
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
                      intro _composition_input _preimage_domain
                      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                      rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
                      simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) _value_i10 _value_i11 (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])))) (by
                      rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
                      let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
                      have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
                      have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
                      have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                                exact h_1118)
                            )
                        )
                      have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                                exact h_1119)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                          let _atomic_wd_2_0 := _object_w40
                          exact (by
                            let _litex_return_call := _object_w40
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _object_w40 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w40 (h_43 (M := M)) (by
                          let _atomic_wd_2_0 := _object_w40
                          exact (by
                            let _litex_return_call := _object_w40
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
                    Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
                      have _composition_checked : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i29 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => (((¬ (_raw_i29 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i28 = (M.number (0 : ℂ))))))) _raw_i28 _raw_i29) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i28, _raw_i29])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
                      rintro _raw_i28 _raw_i29 h_1197 h_1198 ⟨h_1118, h_1119⟩
                      let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_1197)
                      have h_1197 : Litex.In _value_i28 (Litex.R (M := M)) := h_1197
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_1198)
                      have h_1198 : Litex.In _value_i29 (Litex.R (M := M)) := h_1198
                      have h_1118 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i29 = (M.number (0 : ℂ))))
                                exact h_1118)
                            )
                        )
                      have h_1119 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i28 = (M.number (0 : ℂ))))
                                exact h_1119)
                            )
                        )
                      let _composition_call := (let _object_w39 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i28 _value_i29 (h_223 (M := M)) h_1197 h_1198 (And.intro h_1118 h_1119));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w39 (h_43 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w39
                      exact (by
                        let _litex_return_call := _object_w39
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
                      exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
                      intro _composition_input _preimage_domain
                      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                      rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
                      simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) h_1115 h_1116 (And.intro h_226 h_225))
                    have h_229 : (by
                      let _atomic_wd_1_0 := _object_w41
                      exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w41
                              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.FunctionSemantics.call_mem ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => (((¬ (_raw_i35 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i34 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => (((¬ (_raw_i35 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i34 = (M.number (0 : ℂ))))))))).output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.composeInFnSet (_atomic_wd_1_0).val.function (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => (((¬ (_raw_i35 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i34 = (M.number (0 : ℂ))))))) (Litex.denote _value_i10) (Litex.denote _value_i11)).mpr ⟨h_1115, h_1116, (And.intro h_226 h_225)⟩))))
                          )
                      )
                    exact h_229
                  )
                )
            )
          exact (by
          let _source_signature := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))
          have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.composeInFnSet (let _composition_lambda := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, _raw_i19])))) (by
          rintro _raw_i18 _raw_i19 h_701 h_702 ⟨h_626, h_627⟩
          let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_701)
          have h_701 : Litex.In _value_i18 (Litex.R (M := M)) := h_701
          let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_702)
          have h_702 : Litex.In _value_i19 (Litex.R (M := M)) := h_702
          have h_626 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i19 = (M.number (0 : ℂ))))
                    exact h_626)
                )
            )
          have h_627 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i18 = (M.number (0 : ℂ))))
                    exact h_627)
                )
            )
          change (by
            let _atomic_wd_1_0 := (let _object_w32 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i18 _value_i19 (h_223 (M := M)) h_701 h_702 (And.intro h_626 h_627));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w32 (h_43 (M := M)) (by
              let _atomic_wd_2_0 := _object_w32
              exact (by
                let _litex_return_call := _object_w32
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _object_w32 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i18 _value_i19 (h_223 (M := M)) h_701 h_702 (And.intro h_626 h_627));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w32 (h_43 (M := M)) (by
              let _atomic_wd_2_0 := _object_w32
              exact (by
                let _litex_return_call := _object_w32
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
        Litex.compose (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by
          have _composition_checked : ∀ (_raw_i18 : M.Value) (_raw_i19 : M.Value), M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i19 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) _raw_i18 _raw_i19) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i18, _raw_i19])) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain := (by
          rintro _raw_i18 _raw_i19 h_701 h_702 ⟨h_626, h_627⟩
          let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_701)
          have h_701 : Litex.In _value_i18 (Litex.R (M := M)) := h_701
          let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_702)
          have h_702 : Litex.In _value_i19 (Litex.R (M := M)) := h_702
          have h_626 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i19 = (M.number (0 : ℂ))))
                    exact h_626)
                )
            )
          have h_627 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i18 = (M.number (0 : ℂ))))
                    exact h_627)
                )
            )
          let _composition_call := (let _object_w31 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (_object_i3 (M := M)) _value_i18 _value_i19 (h_223 (M := M)) h_701 h_702 (And.intro h_626 h_627));
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w31 (h_43 (M := M)) (by
          let _atomic_wd_1_0 := _object_w31
          exact (by
            let _litex_return_call := _object_w31
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
          exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
          intro _composition_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
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
          simpa only [← _composition_repack] using (_composition_checked (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _composition_input (M.number (2 : ℂ))) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (0 : Fin 2) (1 : ℂ) (by norm_num)) (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members (1 : Fin 2) (2 : ℂ) (by norm_num)) (And.intro _preimage_guard_0 _preimage_guard_1)))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) ((h_224 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))))
          have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _domain_target := h_1025 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
        ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i11 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
          have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
          have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        ))
          have _domain_target := h_1067 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
          apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
          apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
          funext i
          fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => (((¬ (_raw_i19 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
        ) x hx⟩))
          change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
          have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
          rw [_same_domain] at _source_graph
          apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
          intro _input _hin
          change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
          obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
          obtain ⟨_raw_0, _member_0, _raw_1, _member_1, rfl⟩ := (Litex.FiniteFunction.cart2_members _ _ _).mp _members
          simp only [Litex.FiniteFunction.unpack_pack2] at _guard
          let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
          let _arg_1 := Litex.semanticObject (M := M) _raw_1 (M.member_isSet _member_1)
          exact h_228 _arg_0 _member_0 _arg_1 _member_1 (And.left _guard) (And.right _guard))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_composed_x5f_quotient_x5f_membership_x2f_statement_x2e_lit
