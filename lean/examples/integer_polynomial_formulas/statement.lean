import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
  change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.Z (M := M))
  exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_57 : Litex.In (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_56 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_56)
    have h_56 : Litex.In _value_i2 (Litex.Z (M := M)) := h_56
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_58 : Litex.Same (_object_i1 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
  change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.Z (M := M))
  exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (1 : ℂ) (1 : ℤ) (by norm_num)))))) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_72 h_73 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
  have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
  have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
  change Litex.In (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73)) (Litex.Z (M := M))
  exact (Litex.subInZ _value_i4 _value_i5 h_72 h_73)))
theorem h_177 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i5 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → True := by
    intro _raw_i4 _raw_i5 h_175 h_176 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_175)
    have h_175 : Litex.In _value_i4 (Litex.Z (M := M)) := h_175
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_176)
    have h_176 : Litex.In _value_i5 (Litex.Z (M := M)) := h_176
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_178 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_72 h_73 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
  have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
  have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
  change Litex.In (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73)) (Litex.Z (M := M))
  exact (Litex.subInZ _value_i4 _value_i5 h_72 h_73))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

noncomputable def _object_i6 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by
  intro _raw_i7 _raw_i8 h_192 h_193 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_192)
  have h_192 : Litex.In _value_i7 (Litex.Z (M := M)) := h_192
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_193)
  have h_193 : Litex.In _value_i8 (Litex.Z (M := M)) := h_193
  change Litex.In (Litex.mul _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_192) (Litex.integerToComplex _value_i8 h_193)) (Litex.Z (M := M))
  exact (Litex.mulInZ _value_i7 _value_i8 h_192 h_193)))
theorem h_317 : Litex.In (_object_i6 (M := M)) (by
  have _checked_header : ∀ (_raw_i7 : M.Value) (_raw_i8 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i8 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _raw_i7 _raw_i8) → True := by
    intro _raw_i7 _raw_i8 h_315 h_316 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_315)
    have h_315 : Litex.In _value_i7 (Litex.Z (M := M)) := h_315
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_316)
    have h_316 : Litex.In _value_i8 (Litex.Z (M := M)) := h_316
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i6 (M := M)))
theorem h_318 : Litex.Same (_object_i6 (M := M)) (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by
  intro _raw_i7 _raw_i8 h_192 h_193 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_192)
  have h_192 : Litex.In _value_i7 (Litex.Z (M := M)) := h_192
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_193)
  have h_193 : Litex.In _value_i8 (Litex.Z (M := M)) := h_193
  change Litex.In (Litex.mul _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_192) (Litex.integerToComplex _value_i8 h_193)) (Litex.Z (M := M))
  exact (Litex.mulInZ _value_i7 _value_i8 h_192 h_193))) :=
  (Litex.sameRefl (_object_i6 (M := M)))

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by
  intro _raw_i10 h_332 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_332)
  have h_332 : Litex.In _value_i10 (Litex.Z (M := M)) := h_332
  change Litex.In (Litex.neg _value_i10 (Litex.integerToComplex _value_i10 h_332)) (Litex.Z (M := M))
  exact (Litex.negInZ _value_i10 h_332)))
theorem h_403 : Litex.In (_object_i9 (M := M)) (by
  have _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := by
    intro _raw_i10 h_402 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_402)
    have h_402 : Litex.In _value_i10 (Litex.Z (M := M)) := h_402
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i9 (M := M)))
theorem h_404 : Litex.Same (_object_i9 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by
  intro _raw_i10 h_332 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_332)
  have h_332 : Litex.In _value_i10 (Litex.Z (M := M)) := h_332
  change Litex.In (Litex.neg _value_i10 (Litex.integerToComplex _value_i10 h_332)) (Litex.Z (M := M))
  exact (Litex.negInZ _value_i10 h_332))) :=
  (Litex.sameRefl (_object_i9 (M := M)))

noncomputable def _object_i11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by
  intro _raw_i12 h_418 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_418)
  have h_418 : Litex.In _value_i12 (Litex.Z (M := M)) := h_418
  change Litex.In (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.Z (M := M))
  exact (Litex.powStructuralInZ (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_418 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))))))
theorem h_527 : Litex.In (_object_i11 (M := M)) (by
  have _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := by
    intro _raw_i12 h_526 _
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_526)
    have h_526 : Litex.In _value_i12 (Litex.Z (M := M)) := h_526
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i11 (M := M)))
theorem h_528 : Litex.Same (_object_i11 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by
  intro _raw_i12 h_418 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_418)
  have h_418 : Litex.In _value_i12 (Litex.Z (M := M)) := h_418
  change Litex.In (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.Z (M := M))
  exact (Litex.powStructuralInZ (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_418 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num)))))) :=
  (Litex.sameRefl (_object_i11 (M := M)))

theorem h_529 : Litex.Same (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro) (Litex.number (M := M) (3 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
      change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.Z (M := M))
      exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (1 : ℂ) (1 : ℤ) (by norm_num)))))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
      intro _raw_i2 h_14 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
      change Litex.In (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.Z (M := M))
      exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (1 : ℂ) (1 : ℤ) (by norm_num))))))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_58 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))

theorem h_619 : Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) (5 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (5 : ℂ) (5 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro) (Litex.number (M := M) (3 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FunctionSemantics.pairValue (M := M) (M.number (5 : ℂ)) (M.number (2 : ℂ)))))).trans (by
    let _litex_original := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) (5 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (5 : ℂ) (5 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
      intro _raw_i4 _raw_i5 h_72 h_73 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
      have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
      have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
      change Litex.In (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73)) (Litex.Z (M := M))
      exact (Litex.subInZ _value_i4 _value_i5 h_72 h_73))) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
      intro _raw_i4 _raw_i5 h_72 h_73 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
      have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
      have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
      change Litex.In (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73)) (Litex.Z (M := M))
      exact (Litex.subInZ _value_i4 _value_i5 h_72 h_73)))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) (5 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (5 : ℂ) (5 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_178 (M := M))) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FunctionSemantics.pairValue (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).1 (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FunctionSemantics.unpair_pair] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((5 : ℂ) - (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (5 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))

theorem h_845 : Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (h_317 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (3 : ℂ) (3 : ℤ) (by norm_num))) True.intro) (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FunctionSemantics.pairValue (M := M) (M.negValue (M.number (2 : ℂ))) (M.number (3 : ℂ)))))).trans (by
    let _litex_original := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (h_317 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (3 : ℂ) (3 : ℤ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_192 h_193 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_192)
      have h_192 : Litex.In _value_i7 (Litex.Z (M := M)) := h_192
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_193)
      have h_193 : Litex.In _value_i8 (Litex.Z (M := M)) := h_193
      change Litex.In (Litex.mul _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_192) (Litex.integerToComplex _value_i8 h_193)) (Litex.Z (M := M))
      exact (Litex.mulInZ _value_i7 _value_i8 h_192 h_193))) (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_192 h_193 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_192)
      have h_192 : Litex.In _value_i7 (Litex.Z (M := M)) := h_192
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_193)
      have h_193 : Litex.In _value_i8 (Litex.Z (M := M)) := h_193
      change Litex.In (Litex.mul _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_192) (Litex.integerToComplex _value_i8 h_193)) (Litex.Z (M := M))
      exact (Litex.mulInZ _value_i7 _value_i8 h_192 h_193)))) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (3 : ℂ) (3 : ℤ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (((Litex.sameRefl (_object_i6 (M := M)))).trans (h_318 (M := M))) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FunctionSemantics.pairValue (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).1 (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FunctionSemantics.unpair_pair] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.negValue (M.number (2 : ℂ))) (M.number (3 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ))) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ))) ((- (2 : ℂ)) * (3 : ℂ)) (- (6 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ))) (Litex.numberInC (M := M) (3 : ℂ)) (- (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (6 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (by norm_num)))

theorem h_1578 : Litex.Same (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_403 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro) (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_403 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by
      intro _raw_i10 h_332 _
      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_332)
      have h_332 : Litex.In _value_i10 (Litex.Z (M := M)) := h_332
      change Litex.In (Litex.neg _value_i10 (Litex.integerToComplex _value_i10 h_332)) (Litex.Z (M := M))
      exact (Litex.negInZ _value_i10 h_332))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by
      intro _raw_i10 h_332 _
      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_332)
      have h_332 : Litex.In _value_i10 (Litex.Z (M := M)) := h_332
      change Litex.In (Litex.neg _value_i10 (Litex.integerToComplex _value_i10 h_332)) (Litex.Z (M := M))
      exact (Litex.negInZ _value_i10 h_332)))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (2 : ℂ) (2 : ℤ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i9 (M := M)))).trans (h_404 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (Litex.denote _litex_literal.val.argument) = (M.negValue (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.sameRefl (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))))

theorem h_1981 : Litex.Same (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (h_527 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro) (Litex.number (M := M) (9 : ℂ)) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.negValue (M.number (3 : ℂ)))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (h_527 (M := M)) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro)
    let _litex_literal := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by
      intro _raw_i12 h_418 _
      let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_418)
      have h_418 : Litex.In _value_i12 (Litex.Z (M := M)) := h_418
      change Litex.In (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.Z (M := M))
      exact (Litex.powStructuralInZ (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_418 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num)))))) (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by
      intro _raw_i12 h_418 _
      let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_418)
      have h_418 : Litex.In _value_i12 (Litex.Z (M := M)) := h_418
      change Litex.In (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.Z (M := M))
      exact (Litex.powStructuralInZ (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_418 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro)
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i11 (M := M)))).trans (h_528 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.NativeBridge.sameOfDenoteNumber (Litex.powNatReal (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.number (M := M) (9 : ℂ)) ((- (3 : ℂ)) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (- (3 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num)))
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit
