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
  exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))))
theorem h_57 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_58 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_72 h_73 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_72)
  have h_72 : Litex.In _value_i4 (Litex.Z (M := M)) := h_72
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_73)
  have h_73 : Litex.In _value_i5 (Litex.Z (M := M)) := h_73
  change Litex.In (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_72) (Litex.integerToComplex _value_i5 h_73)) (Litex.Z (M := M))
  exact (Litex.subInZ _value_i4 _value_i5 h_72 h_73)))
theorem h_177 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_178 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

noncomputable def _object_i6 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by
  intro _raw_i7 _raw_i8 h_192 h_193 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_192)
  have h_192 : Litex.In _value_i7 (Litex.Z (M := M)) := h_192
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_193)
  have h_193 : Litex.In _value_i8 (Litex.Z (M := M)) := h_193
  change Litex.In (Litex.mul _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_192) (Litex.integerToComplex _value_i8 h_193)) (Litex.Z (M := M))
  exact (Litex.mulInZ _value_i7 _value_i8 h_192 h_193)))
theorem h_317 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i6 (M := M)))
theorem h_318 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (Litex.sameRefl (_object_i6 (M := M)))

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by
  intro _raw_i10 h_332 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_332)
  have h_332 : Litex.In _value_i10 (Litex.Z (M := M)) := h_332
  change Litex.In (Litex.neg _value_i10 (Litex.integerToComplex _value_i10 h_332)) (Litex.Z (M := M))
  exact (Litex.negInZ _value_i10 h_332)))
theorem h_403 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i9 (M := M)))
theorem h_404 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (Litex.sameRefl (_object_i9 (M := M)))

noncomputable def _object_i11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by
  intro _raw_i12 h_418 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_418)
  have h_418 : Litex.In _value_i12 (Litex.Z (M := M)) := h_418
  change Litex.In (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.Z (M := M))
  exact (by
    let _litex_power := (Litex.powNatReal _value_i12 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i12 h_418) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    have _elaborated_power_base := h_418
    have _elaborated_power_exponent := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
    exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
  )))
theorem h_527 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i11 (M := M)))
theorem h_528 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (Litex.sameRefl (_object_i11 (M := M)))

noncomputable def _object_w21 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)

theorem h_529 : Litex.Same (_object_w21 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) from by
    have _litex_residual : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.number (3 : ℂ)) := (Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_58 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  ))).trans _litex_residual)

noncomputable def _object_w23 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)

theorem h_619 : Litex.Same (_object_w23 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (5 : ℂ)), (M.number (2 : ℂ))])) = (M.number (3 : ℂ)) from by
    have _litex_residual : (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) := (Litex.NativeBridge.sameOfDenoteNumber (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((5 : ℂ) - (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (5 : ℂ)), (M.number (2 : ℂ))])))).trans (by
    let _litex_original := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_177 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_178 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.subValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)

noncomputable def _object_w33 := (let _object_w24 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w24 _wd_1_1 (h_317 (M := M)) (Litex.NativeBridge.inOfDenoteNumber _object_w24 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w24).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))

noncomputable def _object_w34 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)))

theorem h_845 : Litex.Same (_object_w33 (M := M)) (_object_w34 (M := M)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (2 : ℂ))), (M.number (3 : ℂ))])) = (M.negValue (M.number (6 : ℂ))) from by
    have _litex_residual : (M.mulValue (M.negValue (M.number (2 : ℂ))) (M.number (3 : ℂ))) = (M.negValue (M.number (6 : ℂ))) := (Litex.NativeBridge.sameOfDenoteNumber (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ))) (Litex.numberInC (M := M) (3 : ℂ)))) (_object_w34 (M := M)) ((- (2 : ℂ)) * (3 : ℂ)) (- (6 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber ((_object_w33 (M := M))).val.first (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ))) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (by norm_num))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (2 : ℂ))), (M.number (3 : ℂ))])))).trans (by
    let _litex_original := (let _object_w31 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w31 _wd_1_1 (h_317 (M := M)) (Litex.NativeBridge.inOfDenoteNumber _object_w31 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w31).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
    let _litex_literal := (let _wd_1_0 := (_object_i6 (M := M));
    let _object_w32 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
    let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_1_0 _object_w32 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.inOfDenoteNumber _object_w32 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w32).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_318 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.mulValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.negValue (M.number (2 : ℂ))) (M.number (3 : ℂ))) from rfl))
  ))).trans _litex_residual)

noncomputable def _object_w35 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_403 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)

noncomputable def _object_w36 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_1479 : Litex.Same (_object_w35 (M := M)) (_object_w36 (M := M)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (2 : ℂ))) = (M.negValue (M.number (2 : ℂ))) from by
    have _litex_residual : (M.negValue (M.number (2 : ℂ))) = (M.negValue (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_403 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_404 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.negValue _raw_i10)) (Litex.denote _litex_literal.val.argument) = (M.negValue (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)

noncomputable def _object_w42 := (let _object_w37 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
(Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w37 (h_527 (M := M)) (Litex.NativeBridge.inOfDenoteNumber _object_w37 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_object_w37).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro))

theorem h_1882 : Litex.Same (_object_w42 (M := M)) (Litex.number (M := M) (9 : ℂ)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.negValue (M.number (3 : ℂ)))) = (M.number (9 : ℂ)) from by
    have _litex_residual : (M.powValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))) = (M.number (9 : ℂ)) := (Litex.NativeBridge.sameOfDenoteNumber (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.number (M := M) (9 : ℂ)) ((- (3 : ℂ)) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.inOfDenoteNumber ((_object_w42 (M := M))).val.argument (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.negValue (M.number (3 : ℂ)))))).trans (by
    let _litex_original := (let _object_w40 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w40 (h_527 (M := M)) (Litex.NativeBridge.inOfDenoteNumber _object_w40 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_object_w40).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro))
    let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
    let _object_w41 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) _wd_1_0 _object_w41 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.inOfDenoteNumber _object_w41 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_object_w41).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_528 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (M.powValue _raw_i12 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_polynomial_x5f_formulas_x2f_statement_x2e_lit
