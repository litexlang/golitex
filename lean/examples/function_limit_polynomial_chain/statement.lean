import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_polynomial_x5f_chain_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change Litex.In _value_i2 (Litex.R (M := M))
  exact h_14))
theorem h_21 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_22 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_36 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_36)
  have h_36 : Litex.In _value_i4 (Litex.R (M := M)) := h_36
  change (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_36 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i4 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_36 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_36
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ))))
theorem h_74 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_75 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.number (1 : ℂ))) (by
  intro _raw_i6 h_89 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_89)
  have h_89 : Litex.In _value_i6 (Litex.R (M := M)) := h_89
  change Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M))
  exact (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
theorem h_98 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_99 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_i7 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.number (2 : ℂ))) (by
  intro _raw_i8 h_113 _
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_113)
  have h_113 : Litex.In _value_i8 (Litex.R (M := M)) := h_113
  change Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M))
  exact (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))
theorem h_124 : Litex.In (_object_i7 (M := M)) (Litex.fnSet ((_object_i7 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i7 (M := M)))
      )
  )
theorem h_125 : Litex.Same (_object_i7 (M := M)) (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i7 (M := M)))
      )
  )

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue (M.powValue _raw_i10 (M.number (2 : ℂ))) (M.number (1 : ℂ)))) (by
  intro _raw_i10 h_139 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_139)
  have h_139 : Litex.In _value_i10 (Litex.R (M := M)) := h_139
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i10 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_139 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_139)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i10 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_139 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_139)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))))
    exact (Litex.addInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.left
      have _elaborated_power_base := h_139
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_349 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i9 (M := M)))
      )
  )
theorem h_350 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i9 (M := M)))
      )
  )

noncomputable def _object_i11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.subValue _raw_i12 (M.number (2 : ℂ)))) (by
  intro _raw_i12 h_364 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_364)
  have h_364 : Litex.In _value_i12 (Litex.R (M := M)) := h_364
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i12 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_364) (Litex.numberInC (M := M) (2 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i12 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_364) (Litex.numberInC (M := M) (2 : ℂ)))
    exact (Litex.subInR _value_i12 (Litex.number (M := M) (2 : ℂ)) h_364 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))))
theorem h_478 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i11 (M := M)))
      )
  )
theorem h_479 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i11 (M := M)))
      )
  )

noncomputable def _object_i13 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (M.mulValue (M.addValue (M.powValue _raw_i14 (M.number (2 : ℂ))) (M.number (1 : ℂ))) (M.subValue _raw_i14 (M.number (2 : ℂ))))) (by
  intro _raw_i14 h_493 _
  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_493)
  have h_493 : Litex.In _value_i14 (Litex.R (M := M)) := h_493
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.powNatReal _value_i14 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_493 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_493)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := (Litex.sub _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_493) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
        let _litex_power := (_atomic_wd_2_0).val.left
        have _elaborated_power_base := (M.real_subset_complex _ h_493)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_493) (Litex.numberInC (M := M) (2 : ℂ))))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.powNatReal _value_i14 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_493 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_493)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := (Litex.sub _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_493) (Litex.numberInC (M := M) (2 : ℂ)));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
        let _litex_power := (_atomic_wd_2_0).val.left
        have _elaborated_power_base := (M.real_subset_complex _ h_493)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.subInC _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_493) (Litex.numberInC (M := M) (2 : ℂ))))))
    exact (Litex.mulInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInR ((_atomic_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (by
      let _litex_power := ((_atomic_wd_1_0).val.left).val.left
      have _elaborated_power_base := h_493
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.subInR _value_i14 (Litex.number (M := M) (2 : ℂ)) h_493 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))))))
theorem h_1430 : Litex.In (_object_i13 (M := M)) (Litex.fnSet ((_object_i13 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i13 (M := M)))
      )
  )
theorem h_1431 : Litex.Same (_object_i13 (M := M)) (_object_i13 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i13 (M := M)))
      )
  )

theorem h_1437 : ∀ (_value_i15 : Litex.Obj (M := M) M.Value) (h_2707 : Litex.In _value_i15 (Litex.RPos (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_2711 : Litex.In _value_i16 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i16 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_2711) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i16 (Litex.number (M := M) (2 : ℂ)) h_2711 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i16 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_2711) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i16 (Litex.number (M := M) (2 : ℂ)) h_2711 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))))) _value_i15)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1432 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          exact (show ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_1452 : Litex.In _value_i15 (Litex.RPos (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_1456 : Litex.In _value_i16 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i16 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_1456) (Litex.numberInC (M := M) (2 : ℂ)));
        (Litex.abs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.subInR _value_i16 (Litex.number (M := M) (2 : ℂ)) h_1456 h_1432))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i16 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_1456) (Litex.numberInC (M := M) (2 : ℂ)));
        (Litex.abs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.subInR _value_i16 (Litex.number (M := M) (2 : ℂ)) h_1456 h_1432)))) _value_i15)) from (by
          intro _Host _rep _radius _radius_member
          obtain ⟨_input, _input_member, _positive, _near⟩ := Litex.realFiniteLimitAccumulation .both (Litex.number (M := M) (2 : ℂ)) h_1432 _radius _radius_member
          exact ⟨_input, _input_member, _positive, _near⟩
        ))
        )
      )
  )

theorem h_3878 : Litex.HasFiniteFunctionLimit .both (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_3866 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_20 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
            exact Litex.In (_object_i1 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_20 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                        have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                    exact (h_21 (M := M)))
                )
            )
          have h_3867 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_3868 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3867
                )
            )
          have h_3869 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_3870 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3869
                )
            )
          have h_3875 : ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_3919 : Litex.In _value_i17 (Litex.RPos (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_3923 : Litex.In _value_i18 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i18 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_3923) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i18 (Litex.number (M := M) (2 : ℂ)) h_3923 h_3869))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i18 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_3923) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i18 (Litex.number (M := M) (2 : ℂ)) h_3923 h_3869)))) _value_i17)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i17 _rep_i17 _value_i17 h_3919
                    have h_3920 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i17 h_3919)
                          )
                      )
                    have h_3921 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i17 h_3920)
                          )
                      )
                    have h_3922 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i17 h_3920) _litex_zero.symm)
                          )
                      )
                    exact ((h_1437 (M := M)) (Litex.semanticObject (Litex.denote _value_i17) (Litex.isSet _value_i17)) h_3919)
                  )
                )
            )
          have h_3877 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_5678 : Litex.In _value_i19 (Litex.R (M := M))), (by
            let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 h_3866 h_5678 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w40
              exact Litex.Same _equal_wd_1_0 _value_i19)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i19 _rep_i19 _value_i19 h_5678
                    let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 h_3866 h_5678 True.intro)
                    have h_3876 : (by
                      let _equal_wd_1_0 := _object_w40
                      exact Litex.Same _equal_wd_1_0 _value_i19) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w40;
                            (show Litex.Same _equal_wd_1_0 _value_i19 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (Litex.denote _value_i19) from by
                              have _litex_residual : (Litex.denote _value_i19) = (Litex.denote _value_i19) := (show @Eq M.Value _ _ from Eq.refl _)
                              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (Litex.denote _value_i19) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := _value_i19;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_5678 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i19) from rfl))
                            ))).trans _litex_residual)))
                          )
                      )
                    exact h_3876
                  )
                )
            )
          exact (show (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
            have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_3867
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_3867
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_5727 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_3869
          have h_5734 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_3869
          exact Litex.HasFiniteFunctionLimit .both (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ))) from (by
          let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
          have _member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          let _source_domain := (M.standard Litex.StandardSetValue.real)
          have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
          have _domain_match : _source_domain = _signature.domain := by
            apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _domain := Litex.semanticObject _source_domain _domain_set
          have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
          let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
          have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_3867
          have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_3867
          refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
          intro x hx
          exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
        )
          exact Litex.finiteFunctionLimitIdentity .both (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_3869 h_3875 h_3877
        ))
        )
      )
  )

theorem h_5789 : Litex.HasFiniteFunctionLimit .both (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_5775 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_20 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
            exact Litex.In (_object_i1 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_20 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                        have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                    exact (h_21 (M := M)))
                )
            )
          have h_5776 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_5777 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5776
                )
            )
          have h_5778 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_5781 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_73 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
                have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
            exact Litex.In (_object_i3 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_73 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
                        have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                    exact (h_74 (M := M)))
                )
            )
          have h_5782 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5776
                )
            )
          have h_5783 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5776
                )
            )
          have h_5784 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_5785 : Litex.HasFiniteFunctionLimit .both (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3878 (M := M))
                )
            )
          have h_5786 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_5873 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_5786)
                )
            )
          have h_5788 : ∀ {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_5919 : Litex.In _value_i22 (Litex.R (M := M))), (by
            let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i22 h_5781 h_5919 True.intro)
            let _object_w46 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 h_5775 h_5919 True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) h_5786 (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (by
              let _equal_wd_1_0 := _object_w45
              let _equal_wd_1_1 := _object_w46
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i22 _rep_i22 _value_i22 h_5919
                    let _object_w45 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i22 h_5781 h_5919 True.intro)
                    let _object_w46 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 h_5775 h_5919 True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) h_5786 (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    have h_5787 : (by
                      let _equal_wd_1_0 := _object_w45
                      let _equal_wd_1_1 := _object_w46
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w45;
                            let _equal_wd_1_1 := _object_w46;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i22)) = (M.powValue (Litex.denote _value_i22) (M.number (2 : ℂ))) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                              let _wd_1_1 := _value_i22;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_5919 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_75 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (Litex.denote _value_i22) (M.number (2 : ℂ))) from rfl))
                            )).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i22)) = (Litex.denote _value_i22) from by
                              let _litex_original := (_equal_wd_1_1).val.base
                              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := _value_i22;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_5919 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i22) from rfl))
                            ) (Eq.refl (M.number (2 : ℂ))))).symm))))
                          )
                      )
                    exact h_5787
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_2 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_5778 h_5786 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))
            have _limit_function : Litex.In (_object_i3 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_75 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_5776
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_5776
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_15211 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_5778
          have h_15218 : (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_5778 h_5786 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℝ) (by norm_num))))
          exact Litex.HasFiniteFunctionLimit .both (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_2) from (by
          let _law0_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
            intro _raw_i2 h_20 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
            have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
          have _law0_member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _law0_signature) := h_5775
          let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
          have _law_real_0 : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := by
            refine ⟨_law0_signature, _law0_member, ?_, h_5777⟩
            intro x hx
            exact h_5776 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i1 (M := M))) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
          let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
            intro _raw_i4 h_73 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
            have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
          have _law1_member : Litex.In (_object_i3 (M := M)) (Litex.fnSet _law1_signature) := h_5781
          let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
          have _law_real_1 : Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) := by
            refine ⟨_law1_signature, _law1_member, ?_, h_5783⟩
            intro x hx
            exact h_5782 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i3 (M := M))) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
          let _law_parameter := Litex.NativeBridge.asNat (Litex.number (M := M) (2 : ℂ)) h_5786
          have _law_parameter_value : Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asNat_spec (Litex.number (M := M) (2 : ℂ)) h_5786
          exact Litex.finiteFunctionLimitMap .both (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i3 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_5778 h_5786 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _law_real_0 _law_real_1 (_law_domain_1.symm.trans (h_5784.trans _law_domain_0)) (fun value => M.powValue value (Litex.denote (Litex.number (M := M) (2 : ℂ)))) (fun x : ℝ => x^_law_parameter) (by intro x; rw [_law_parameter_value, M.pow_numbers_nat, Complex.ofReal_pow]) rfl (by
            intro input hinput
            have _law_input : M.mem input (Litex.denote _law0_domain) := by
              rw [_law_domain_0]
              exact hinput
            exact h_5788 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
          ) (continuous_id.pow _law_parameter) h_5785
        ))
        )
      )
  )

theorem h_15368 : Litex.HasFiniteFunctionLimit .both (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_15356 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_97 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_97)
                have h_97 : Litex.In _value_i6 (Litex.R (M := M)) := h_97
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
            exact Litex.In (_object_i5 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_97 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_97)
                        have h_97 : Litex.In _value_i6 (Litex.R (M := M)) := h_97
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
                    exact (h_98 (M := M)))
                )
            )
          have h_15357 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_15358 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15357
                )
            )
          have h_15359 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_15360 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_15365 : ∀ {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_15425 : Litex.In _value_i27 (Litex.RPos (M := M))), ∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (h_15429 : Litex.In _value_i28 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i28 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_15429) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i28 (Litex.number (M := M) (2 : ℂ)) h_15429 h_15359))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i28 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_15429) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i28 (Litex.number (M := M) (2 : ℂ)) h_15429 h_15359)))) _value_i27)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i27 _rep_i27 _value_i27 h_15425
                    have h_15426 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i27 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i27 h_15425)
                          )
                      )
                    have h_15427 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i27 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i27 h_15426)
                          )
                      )
                    have h_15428 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i27 h_15426) _litex_zero.symm)
                          )
                      )
                    exact ((h_1437 (M := M)) (Litex.semanticObject (Litex.denote _value_i27) (Litex.isSet _value_i27)) h_15425)
                  )
                )
            )
          have h_15367 : ∀ {_Host_i29 : Type _} [_rep_i29 : Litex.Representation M _Host_i29] (_value_i29 : Litex.Obj (M := M) _Host_i29) (h_17180 : Litex.In _value_i29 (Litex.R (M := M))), (by
            let _object_w52 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i29 h_15356 h_17180 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w52
              exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i29 _rep_i29 _value_i29 h_17180
                    let _object_w52 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i29 h_15356 h_17180 True.intro)
                    have h_15366 : (by
                      let _equal_wd_1_0 := _object_w52
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w52;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i29)) = (M.number (1 : ℂ)) from by
                              have _litex_residual : (M.number (1 : ℂ)) = (M.number (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i29)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i29)) = (M.number (1 : ℂ)) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
                              let _wd_1_1 := _value_i29;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_17180 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_99 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.number (1 : ℂ))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (M.number (1 : ℂ))) (Litex.denote _litex_literal.val.argument) = (M.number (1 : ℂ)) from rfl))
                            ))).trans _litex_residual)))
                          )
                      )
                    exact h_15366
                  )
                )
            )
          exact (show (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i5 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i5 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))
            have _limit_function : Litex.In (_object_i5 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((h_99 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_15357
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_15357
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_17251 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_15359
          have h_17258 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) := h_15360
          exact Litex.HasFiniteFunctionLimit .both (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ))) from (by
          let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))
          have _member : Litex.In (_object_i5 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((h_99 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M))))
          let _source_domain := (M.standard Litex.StandardSetValue.real)
          have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
          have _domain_match : _source_domain = _signature.domain := by
            apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _domain := Litex.semanticObject _source_domain _domain_set
          have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote (_object_i5 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i5 (M := M))) from by
          let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))
          have _limit_function : Litex.In (_object_i5 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((h_99 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M))))
          have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_15357
          have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_15357
          refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
          intro x hx
          exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
        )
          exact Litex.finiteFunctionLimitConstant .both (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_15359 h_15360 h_15365 h_15367
        ))
        )
      )
  )

theorem h_17315 : Litex.HasFiniteFunctionLimit .both (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_17303 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
                intro _raw_i8 h_123 _
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_123)
                have h_123 : Litex.In _value_i8 (Litex.R (M := M)) := h_123
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)))
            exact Litex.In (_object_i7 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
                        intro _raw_i8 h_123 _
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_123)
                        have h_123 : Litex.In _value_i8 (Litex.R (M := M)) := h_123
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)))
                    exact (h_124 (M := M)))
                )
            )
          have h_17304 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_17305 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17304
                )
            )
          have h_17306 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_17307 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17306
                )
            )
          have h_17312 : ∀ {_Host_i32 : Type _} [_rep_i32 : Litex.Representation M _Host_i32] (_value_i32 : Litex.Obj (M := M) _Host_i32) (h_17362 : Litex.In _value_i32 (Litex.RPos (M := M))), ∃ (_value_i33 : Litex.Obj (M := M) M.Value), ∃ (h_17366 : Litex.In _value_i33 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i33 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_17366) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i33 (Litex.number (M := M) (2 : ℂ)) h_17366 h_17306))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i33 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_17366) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i33 (Litex.number (M := M) (2 : ℂ)) h_17366 h_17306)))) _value_i32)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i32 _rep_i32 _value_i32 h_17362
                    have h_17363 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i32 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i32 h_17362)
                          )
                      )
                    have h_17364 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i32 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i32 h_17363)
                          )
                      )
                    have h_17365 : ¬ Litex.Same _value_i32 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i32 h_17363) _litex_zero.symm)
                          )
                      )
                    exact ((h_1437 (M := M)) (Litex.semanticObject (Litex.denote _value_i32) (Litex.isSet _value_i32)) h_17362)
                  )
                )
            )
          have h_17314 : ∀ {_Host_i34 : Type _} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_19157 : Litex.In _value_i34 (Litex.R (M := M))), (by
            let _object_w57 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (_object_i7 (M := M)) _value_i34 h_17303 h_19157 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w57
              exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i34 _rep_i34 _value_i34 h_19157
                    let _object_w57 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (_object_i7 (M := M)) _value_i34 h_17303 h_19157 True.intro)
                    have h_17313 : (by
                      let _equal_wd_1_0 := _object_w57
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w57;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i34)) = (M.number (2 : ℂ)) from by
                              have _litex_residual : (M.number (2 : ℂ)) = (M.number (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i34)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i34)) = (M.number (2 : ℂ)) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                              let _wd_1_1 := _value_i34;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_19157 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_125 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.number (2 : ℂ))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.number (2 : ℂ))) (Litex.denote _litex_literal.val.argument) = (M.number (2 : ℂ)) from rfl))
                            ))).trans _litex_residual)))
                          )
                      )
                    exact h_17313
                  )
                )
            )
          exact (show (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i7 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i7 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))
            have _limit_function : Litex.In (_object_i7 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i7 (M := M)) (_object_i7 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) ((h_125 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i7 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_17304
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_17304
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_19243 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_17306
          have h_19250 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_17306
          exact Litex.HasFiniteFunctionLimit .both (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ))) from (by
          let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))
          have _member : Litex.In (_object_i7 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i7 (M := M)) (_object_i7 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) ((h_125 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i7 (M := M))))
          let _source_domain := (M.standard Litex.StandardSetValue.real)
          have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
          have _domain_match : _source_domain = _signature.domain := by
            apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _domain := Litex.semanticObject _source_domain _domain_set
          have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote (_object_i7 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i7 (M := M))) from by
          let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))
          have _limit_function : Litex.In (_object_i7 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i7 (M := M)) (_object_i7 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True))) ((h_125 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i7 (M := M))))
          have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_17304
          have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_17304
          refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
          intro x hx
          exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
        )
          exact Litex.finiteFunctionLimitConstant .both (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_17306 h_17307 h_17312 h_17314
        ))
        )
      )
  )

theorem h_19314 : Litex.HasFiniteFunctionLimit .both (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_19294 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_73 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
                have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
            exact Litex.In (_object_i3 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_73 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
                        have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                    exact (h_74 (M := M)))
                )
            )
          have h_19295 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_19296 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19295
                )
            )
          have h_19297 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_19300 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_97 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_97)
                have h_97 : Litex.In _value_i6 (Litex.R (M := M)) := h_97
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
            exact Litex.In (_object_i5 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_97 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_97)
                        have h_97 : Litex.In _value_i6 (Litex.R (M := M)) := h_97
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
                    exact (h_98 (M := M)))
                )
            )
          have h_19301 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19295
                )
            )
          have h_19302 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19295
                )
            )
          have h_19303 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_19306 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                intro _raw_i10 h_348 _
                let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
                have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))
            exact Litex.In (_object_i9 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_348 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
                        have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))
                    exact (h_349 (M := M)))
                )
            )
          have h_19307 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19295
                )
            )
          have h_19308 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19295
                )
            )
          have h_19309 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_19310 : (by
            have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) from by
              let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))
              have _limit_function : Litex.In (_object_i3 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_75 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_19295
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_19295
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            )
            have h_19423 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_19297
            have h_19430 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
            exact Litex.HasFiniteFunctionLimit .both (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) from by
                      let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))
                      have _limit_function : Litex.In (_object_i3 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_75 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_19295
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_19295
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_19423 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_19297
                    have h_19430 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i3 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (4 : ℂ)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i3 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) := (h_5789 (M := M))
                      exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i3 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i3 (M := M))) _known_value (Litex.denote (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i3 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _known_value)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.number (M := M) (4 : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) (4 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)))) _known_citation
                    ))
                )
            )
          have h_19311 : Litex.HasFiniteFunctionLimit .both (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_15368 (M := M))
                )
            )
          have h_19313 : ∀ {_Host_i37 : Type _} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (h_19621 : Litex.In _value_i37 (Litex.R (M := M))), (by
            let _object_w60 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i37 h_19306 h_19621 True.intro)
            let _object_w61 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i37 h_19294 h_19621 True.intro);
            let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i37 h_19300 h_19621 True.intro);
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            exact (by
              let _equal_wd_1_0 := _object_w60
              let _equal_wd_1_1 := _object_w61
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i37 _rep_i37 _value_i37 h_19621
                    let _object_w60 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i37 h_19306 h_19621 True.intro)
                    let _object_w61 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i37 h_19294 h_19621 True.intro);
                    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i37 h_19300 h_19621 True.intro);
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    have h_19312 : (by
                      let _equal_wd_1_0 := _object_w60
                      let _equal_wd_1_1 := _object_w61
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w60;
                            let _equal_wd_1_1 := _object_w61;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i37)) = (M.addValue (M.powValue (Litex.denote _value_i37) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
                              let _wd_1_1 := _value_i37;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_19621 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_350 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue (M.powValue _raw_i10 (M.number (2 : ℂ))) (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue (M.powValue _raw_i10 (M.number (2 : ℂ))) (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.powValue (Litex.denote _value_i37) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from rfl))
                            )).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i37)) = (M.powValue (Litex.denote _value_i37) (M.number (2 : ℂ))) from by
                              let _litex_original := (_equal_wd_1_1).val.left
                              let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                              let _wd_1_1 := _value_i37;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_19621 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_75 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.powValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (Litex.denote _value_i37) (M.number (2 : ℂ))) from rfl))
                            ) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i37)) = (M.number (1 : ℂ)) from by
                              let _litex_original := (_equal_wd_1_1).val.right
                              let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
                              let _wd_1_1 := _value_i37;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_19621 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_99 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.number (1 : ℂ))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (M.number (1 : ℂ))) (Litex.denote _litex_literal.val.argument) = (M.number (1 : ℂ)) from rfl))
                            ))).symm))))
                          )
                      )
                    exact h_19312
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_2 := (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))
            have _limit_function : Litex.In (_object_i9 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i9 (M := M)) (_object_i9 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) ((h_350 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i9 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_19295
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_19295
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_23598 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_19297
          have h_23605 : (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((4 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((4 : ℂ) + (1 : ℂ)) (5 : ℝ) (by norm_num))))
          exact Litex.HasFiniteFunctionLimit .both (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_2) from (by
          let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
            intro _raw_i4 h_73 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_73)
            have h_73 : Litex.In _value_i4 (Litex.R (M := M)) := h_73
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
          have _law0_member : Litex.In (_object_i3 (M := M)) (Litex.fnSet _law0_signature) := h_19294
          let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
          have _law_real_0 : Litex.RealFunctionValue M (Litex.denote (_object_i3 (M := M))) := by
            refine ⟨_law0_signature, _law0_member, ?_, h_19296⟩
            intro x hx
            exact h_19295 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i3 (M := M))) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
          let _law1_signature := ((let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
            intro _raw_i6 h_97 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_97)
            have h_97 : Litex.In _value_i6 (Litex.R (M := M)) := h_97
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))).val
          have _law1_member : Litex.In (_object_i5 (M := M)) (Litex.fnSet _law1_signature) := h_19300
          let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
          have _law_real_1 : Litex.RealFunctionValue M (Litex.denote (_object_i5 (M := M))) := by
            refine ⟨_law1_signature, _law1_member, ?_, h_19302⟩
            intro x hx
            exact h_19301 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i5 (M := M))) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
          let _law2_signature := ((let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
            intro _raw_i10 h_348 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
            have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))).val
          have _law2_member : Litex.In (_object_i9 (M := M)) (Litex.fnSet _law2_signature) := h_19306
          let _law2_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law2_domain_set : M.isSet _law2_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law2_domain_match : _law2_source_domain = _law2_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law2_domain_set _law2_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law2_domain := Litex.semanticObject _law2_source_domain _law2_domain_set
          have _law_real_2 : Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) := by
            refine ⟨_law2_signature, _law2_member, ?_, h_19308⟩
            intro x hx
            exact h_19307 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i9 (M := M))) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
          exact Litex.finiteFunctionLimitMapTwo .both (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i5 (M := M))) (Litex.denote (_object_i9 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (4 : ℂ))) (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_19303.trans _law_domain_0)) (_law_domain_2.symm.trans (h_19309.trans _law_domain_0)) M.addValue (fun x y : ℝ => x+y) (by intro x y; rw [M.add_numbers, Complex.ofReal_add]) rfl (by
            intro input hinput
            have _law_input : M.mem input (Litex.denote _law0_domain) := by
              rw [_law_domain_0]
              exact hinput
            exact h_19313 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
          ) (continuous_fst.add continuous_snd) h_19310 h_19311
        ))
        )
      )
  )

theorem h_23792 : Litex.HasFiniteFunctionLimit .both (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_23772 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_20 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
            exact Litex.In (_object_i1 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_20 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                        have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                    exact (h_21 (M := M)))
                )
            )
          have h_23773 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_23774 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23773
                )
            )
          have h_23775 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_23778 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
                intro _raw_i8 h_123 _
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_123)
                have h_123 : Litex.In _value_i8 (Litex.R (M := M)) := h_123
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)))
            exact Litex.In (_object_i7 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
                        intro _raw_i8 h_123 _
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_123)
                        have h_123 : Litex.In _value_i8 (Litex.R (M := M)) := h_123
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)))
                    exact (h_124 (M := M)))
                )
            )
          have h_23779 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23773
                )
            )
          have h_23780 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23773
                )
            )
          have h_23781 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_23784 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                intro _raw_i12 h_477 _
                let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
                have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))
            exact Litex.In (_object_i11 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                        intro _raw_i12 h_477 _
                        let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
                        have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))
                    exact (h_478 (M := M)))
                )
            )
          have h_23785 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23773
                )
            )
          have h_23786 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23773
                )
            )
          have h_23787 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_23788 : Litex.HasFiniteFunctionLimit .both (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3878 (M := M))
                )
            )
          have h_23789 : Litex.HasFiniteFunctionLimit .both (_object_i7 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_17315 (M := M))
                )
            )
          have h_23791 : ∀ {_Host_i44 : Type _} [_rep_i44 : Litex.Representation M _Host_i44] (_value_i44 : Litex.Obj (M := M) _Host_i44) (h_24081 : Litex.In _value_i44 (Litex.R (M := M))), (by
            let _object_w64 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i44 h_23784 h_24081 True.intro)
            let _object_w65 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i44 h_23772 h_24081 True.intro);
            let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (_object_i7 (M := M)) _value_i44 h_23778 h_24081 True.intro);
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            exact (by
              let _equal_wd_1_0 := _object_w64
              let _equal_wd_1_1 := _object_w65
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i44 _rep_i44 _value_i44 h_24081
                    let _object_w64 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i44 h_23784 h_24081 True.intro)
                    let _object_w65 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i44 h_23772 h_24081 True.intro);
                    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (_object_i7 (M := M)) _value_i44 h_23778 h_24081 True.intro);
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    have h_23790 : (by
                      let _equal_wd_1_0 := _object_w64
                      let _equal_wd_1_1 := _object_w65
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w64;
                            let _equal_wd_1_1 := _object_w65;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i44)) = (M.subValue (Litex.denote _value_i44) (M.number (2 : ℂ))) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                              let _wd_1_1 := _value_i44;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_24081 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_479 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.subValue _raw_i12 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (M.subValue _raw_i12 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (Litex.denote _value_i44) (M.number (2 : ℂ))) from rfl))
                            )).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i44)) = (Litex.denote _value_i44) from by
                              let _litex_original := (_equal_wd_1_1).val.left
                              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := _value_i44;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_24081 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i44) from rfl))
                            ) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (Litex.denote _value_i44)) = (M.number (2 : ℂ)) from by
                              let _litex_original := (_equal_wd_1_1).val.right
                              let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
                              let _wd_1_1 := _value_i44;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_24081 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_125 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.number (2 : ℂ))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.number (2 : ℂ))) (Litex.denote _litex_literal.val.argument) = (M.number (2 : ℂ)) from rfl))
                            ))).symm))))
                          )
                      )
                    exact h_23790
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_2 := (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))
            have _limit_function : Litex.In (_object_i11 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i11 (M := M)) (_object_i11 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) ((h_479 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i11 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_23773
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_23773
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_31986 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_23775
          have h_31993 : (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) - (2 : ℂ)) (0 : ℝ) (by norm_num))))
          exact Litex.HasFiniteFunctionLimit .both (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_2) from (by
          let _law0_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
            intro _raw_i2 h_20 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
            have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
          have _law0_member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _law0_signature) := h_23772
          let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
          have _law_real_0 : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := by
            refine ⟨_law0_signature, _law0_member, ?_, h_23774⟩
            intro x hx
            exact h_23773 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i1 (M := M))) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
          let _law1_signature := ((let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
            intro _raw_i8 h_123 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_123)
            have h_123 : Litex.In _value_i8 (Litex.R (M := M)) := h_123
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True)))).val
          have _law1_member : Litex.In (_object_i7 (M := M)) (Litex.fnSet _law1_signature) := h_23778
          let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
          have _law_real_1 : Litex.RealFunctionValue M (Litex.denote (_object_i7 (M := M))) := by
            refine ⟨_law1_signature, _law1_member, ?_, h_23780⟩
            intro x hx
            exact h_23779 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i7 (M := M))) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
          let _law2_signature := ((let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
            intro _raw_i12 h_477 _
            let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
            have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))).val
          have _law2_member : Litex.In (_object_i11 (M := M)) (Litex.fnSet _law2_signature) := h_23784
          let _law2_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law2_domain_set : M.isSet _law2_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law2_domain_match : _law2_source_domain = _law2_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law2_domain_set _law2_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law2_domain := Litex.semanticObject _law2_source_domain _law2_domain_set
          have _law_real_2 : Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) := by
            refine ⟨_law2_signature, _law2_member, ?_, h_23786⟩
            intro x hx
            exact h_23785 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i11 (M := M))) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
          exact Litex.finiteFunctionLimitMapTwo .both (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i7 (M := M))) (Litex.denote (_object_i11 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_23781.trans _law_domain_0)) (_law_domain_2.symm.trans (h_23787.trans _law_domain_0)) M.subValue (fun x y : ℝ => x-y) (by intro x y; rw [M.sub_numbers, Complex.ofReal_sub]) rfl (by
            intro input hinput
            have _law_input : M.mem input (Litex.denote _law0_domain) := by
              rw [_law_domain_0]
              exact hinput
            exact h_23791 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
          ) (continuous_fst.sub continuous_snd) h_23788 h_23789
        ))
        )
      )
  )

theorem h_32185 : Litex.HasFiniteFunctionLimit .both (_object_i13 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_32165 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                intro _raw_i10 h_348 _
                let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
                have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))
            exact Litex.In (_object_i9 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_348 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
                        have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))
                    exact (h_349 (M := M)))
                )
            )
          have h_32166 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_32167 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_32166
                )
            )
          have h_32168 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_32171 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                intro _raw_i12 h_477 _
                let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
                have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))
            exact Litex.In (_object_i11 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                        intro _raw_i12 h_477 _
                        let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
                        have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))
                    exact (h_478 (M := M)))
                )
            )
          have h_32172 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_32166
                )
            )
          have h_32173 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_32166
                )
            )
          have h_32174 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_32177 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                intro _raw_i14 h_1429 _
                let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1429)
                have h_1429 : Litex.In _value_i14 (Litex.R (M := M)) := h_1429
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True)))
            exact Litex.In (_object_i13 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
                        intro _raw_i14 h_1429 _
                        let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1429)
                        have h_1429 : Litex.In _value_i14 (Litex.R (M := M)) := h_1429
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True)))
                    exact (h_1430 (M := M)))
                )
            )
          have h_32178 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_32166
                )
            )
          have h_32179 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_32166
                )
            )
          have h_32180 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          have h_32181 : (by
            have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) from by
              let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))
              have _limit_function : Litex.In (_object_i9 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i9 (M := M)) (_object_i9 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) ((h_350 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i9 (M := M))))
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_32166
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_32166
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            )
            have h_32312 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_32168
            have h_32319 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
            exact Litex.HasFiniteFunctionLimit .both (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) from by
                      let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))
                      have _limit_function : Litex.In (_object_i9 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i9 (M := M)) (_object_i9 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True))) ((h_350 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i9 (M := M))))
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_32166
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_32166
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_32312 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_32168
                    have h_32319 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i9 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (5 : ℂ)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i9 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))))) := (h_19314 (M := M))
                      exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i9 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i9 (M := M))) _known_value (Litex.denote (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i9 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _known_value)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (5 : ℂ)) ((4 : ℂ) + (1 : ℂ)) (5 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num)))) _known_citation
                    ))
                )
            )
          have h_32182 : (by
            have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) from by
              let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))
              have _limit_function : Litex.In (_object_i11 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i11 (M := M)) (_object_i11 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) ((h_479 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i11 (M := M))))
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_32166
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_32166
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            )
            have h_32383 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_32168
            have h_32390 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
            exact Litex.HasFiniteFunctionLimit .both (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) from by
                      let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))
                      have _limit_function : Litex.In (_object_i11 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i11 (M := M)) (_object_i11 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True))) ((h_479 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i11 (M := M))))
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_32166
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_32166
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_32383 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_32168
                    have h_32390 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i11 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (0 : ℂ)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i11 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))))) := (h_23792 (M := M))
                      exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i11 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i11 (M := M))) _known_value (Litex.denote (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i11 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _known_value)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (0 : ℂ)) ((2 : ℂ) - (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) _known_citation
                    ))
                )
            )
          have h_32184 : ∀ {_Host_i51 : Type _} [_rep_i51 : Litex.Representation M _Host_i51] (_value_i51 : Litex.Obj (M := M) _Host_i51) (h_32650 : Litex.In _value_i51 (Litex.R (M := M))), (by
            let _object_w70 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (_object_i13 (M := M)) _value_i51 h_32177 h_32650 True.intro)
            let _object_w71 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i51 h_32165 h_32650 True.intro);
            let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i51 h_32171 h_32650 True.intro);
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            exact (by
              let _equal_wd_1_0 := _object_w70
              let _equal_wd_1_1 := _object_w71
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i51 _rep_i51 _value_i51 h_32650
                    let _object_w70 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (_object_i13 (M := M)) _value_i51 h_32177 h_32650 True.intro)
                    let _object_w71 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i51 h_32165 h_32650 True.intro);
                    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i51 h_32171 h_32650 True.intro);
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    have h_32183 : (by
                      let _equal_wd_1_0 := _object_w70
                      let _equal_wd_1_1 := _object_w71
                      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w70;
                            let _equal_wd_1_1 := _object_w71;
                            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.denote _value_i51)) = (M.mulValue (M.addValue (M.powValue (Litex.denote _value_i51) (M.number (2 : ℂ))) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i51) (M.number (2 : ℂ)))) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i13 (M := M));
                              let _wd_1_1 := _value_i51;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_32650 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_1431 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) (fun (_raw_i14 : M.Value) => (M.mulValue (M.addValue (M.powValue _raw_i14 (M.number (2 : ℂ))) (M.number (1 : ℂ))) (M.subValue _raw_i14 (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) => (M.mulValue (M.addValue (M.powValue _raw_i14 (M.number (2 : ℂ))) (M.number (1 : ℂ))) (M.subValue _raw_i14 (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.addValue (M.powValue (Litex.denote _value_i51) (M.number (2 : ℂ))) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i51) (M.number (2 : ℂ)))) from rfl))
                            )).trans (((show @Eq M.Value _ _ from Eq.refl _)).trans ((congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i51)) = (M.addValue (M.powValue (Litex.denote _value_i51) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from by
                              let _litex_original := (_equal_wd_1_1).val.left
                              let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
                              let _wd_1_1 := _value_i51;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_32650 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_350 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue (M.powValue _raw_i10 (M.number (2 : ℂ))) (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue (M.powValue _raw_i10 (M.number (2 : ℂ))) (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.powValue (Litex.denote _value_i51) (M.number (2 : ℂ))) (M.number (1 : ℂ))) from rfl))
                            ) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i51)) = (M.subValue (Litex.denote _value_i51) (M.number (2 : ℂ))) from by
                              let _litex_original := (_equal_wd_1_1).val.right
                              let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                              let _wd_1_1 := _value_i51;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_32650 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_479 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.subValue _raw_i12 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (M.subValue _raw_i12 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (Litex.denote _value_i51) (M.number (2 : ℂ))) from rfl))
                            ))).symm))))
                          )
                      )
                    exact h_32183
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_2 := (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))
            have _limit_function : Litex.In (_object_i13 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i13 (M := M)) (_object_i13 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) ((h_1431 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i13 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_32166
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_32166
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_47680 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_32168
          have h_47687 : (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
            let _atomic_wd_2_0 := _atomic_wd_1_2
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((5 : ℂ) * (0 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) * (0 : ℂ)) (0 : ℝ) (by norm_num))))
          exact Litex.HasFiniteFunctionLimit .both (_object_i13 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_2) from (by
          let _law0_signature := ((let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
            intro _raw_i10 h_348 _
            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_348)
            have h_348 : Litex.In _value_i10 (Litex.R (M := M)) := h_348
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => True)))).val
          have _law0_member : Litex.In (_object_i9 (M := M)) (Litex.fnSet _law0_signature) := h_32165
          let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
          have _law_real_0 : Litex.RealFunctionValue M (Litex.denote (_object_i9 (M := M))) := by
            refine ⟨_law0_signature, _law0_member, ?_, h_32167⟩
            intro x hx
            exact h_32166 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i9 (M := M))) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
          let _law1_signature := ((let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
            intro _raw_i12 h_477 _
            let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_477)
            have h_477 : Litex.In _value_i12 (Litex.R (M := M)) := h_477
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True)))).val
          have _law1_member : Litex.In (_object_i11 (M := M)) (Litex.fnSet _law1_signature) := h_32171
          let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
          have _law_real_1 : Litex.RealFunctionValue M (Litex.denote (_object_i11 (M := M))) := by
            refine ⟨_law1_signature, _law1_member, ?_, h_32173⟩
            intro x hx
            exact h_32172 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i11 (M := M))) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
          let _law2_signature := ((let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := (by
            intro _raw_i14 h_1429 _
            let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1429)
            have h_1429 : Litex.In _value_i14 (Litex.R (M := M)) := h_1429
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True)))).val
          have _law2_member : Litex.In (_object_i13 (M := M)) (Litex.fnSet _law2_signature) := h_32177
          let _law2_source_domain := (M.standard Litex.StandardSetValue.real)
          have _law2_domain_set : M.isSet _law2_source_domain := (Litex.isSet (Litex.R (M := M)))
          have _law2_domain_match : _law2_source_domain = _law2_signature.domain := by
            apply Litex.SetSemantics.ext _ _ _law2_domain_set _law2_signature.domain_isSet
            intro x
            change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
            rw [Litex.SetSemantics.sep_members]
            exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
          let _law2_domain := Litex.semanticObject _law2_source_domain _law2_domain_set
          have _law_real_2 : Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) := by
            refine ⟨_law2_signature, _law2_member, ?_, h_32179⟩
            intro x hx
            exact h_32178 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote (_object_i13 (M := M))) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
          exact Litex.finiteFunctionLimitMapTwo .both (Litex.denote (_object_i9 (M := M))) (Litex.denote (_object_i11 (M := M))) (Litex.denote (_object_i13 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (5 : ℂ))) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_32174.trans _law_domain_0)) (_law_domain_2.symm.trans (h_32180.trans _law_domain_0)) M.mulValue (fun x y : ℝ => x*y) (by intro x y; rw [M.mul_numbers, Complex.ofReal_mul]) rfl (by
            intro input hinput
            have _law_input : M.mem input (Litex.denote _law0_domain) := by
              rw [_law_domain_0]
              exact hinput
            exact h_32184 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
          ) (continuous_fst.mul continuous_snd) h_32181 h_32182
        ))
        )
      )
  )

theorem h_47854 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) from by
    let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))
    have _limit_function : Litex.In (_object_i13 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i13 (M := M)) (_object_i13 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) ((h_1431 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i13 (M := M))))
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_47866 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
  have h_47881 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
  exact Litex.HasFiniteFunctionLimit .both (_object_i13 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))
            have _limit_function : Litex.In (_object_i13 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i13 (M := M)) (_object_i13 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) ((h_1431 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i13 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_47866 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_47881 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i13 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (0 : ℂ)))) from by
            have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i13 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))))) := (h_32185 (M := M))
            exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i13 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i13 (M := M))) _known_value (Litex.denote (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote (_object_i13 (M := M))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _known_value)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) ((5 : ℂ) * (0 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) _known_citation
          ))
      )
  )

noncomputable def _object_w74 := (let _function := (_object_i13 (M := M)); let _point := (Litex.number (M := M) (2 : ℂ)); Litex.finiteFunctionLimit .both _function _point (show Litex.RealFunctionValue M (Litex.denote (_object_i13 (M := M))) from by
  let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))
  have _limit_function : Litex.In (_object_i13 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i13 (M := M)) (_object_i13 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => True))) ((h_1431 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i13 (M := M))))
  have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
  have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
  refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
  intro x hx
  exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.finiteFunctionConvergentOfCandidate .both _function _point (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (h_32185 (M := M))))

theorem h_47923 : (by
  let _equal_wd_1_0 := (_object_w74 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w74 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from ((Litex.finiteFunctionLimitEqCandidate _equal_wd_1_0 (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (h_32185 (M := M))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ))) (Litex.number (M := M) (0 : ℂ)) ((5 : ℂ) * (0 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_polynomial_x5f_chain_x2f_statement_x2e_lit
